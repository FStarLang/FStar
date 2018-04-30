
open Prims
open FStar_Pervasives

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___72_6 = env
in {FStar_TypeChecker_Env.solver = uu___72_6.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___72_6.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___72_6.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___72_6.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___72_6.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___72_6.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___72_6.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___72_6.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___72_6.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___72_6.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___72_6.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___72_6.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___72_6.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___72_6.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___72_6.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___72_6.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___72_6.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___72_6.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___72_6.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___72_6.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___72_6.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___72_6.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___72_6.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___72_6.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___72_6.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___72_6.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___72_6.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___72_6.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___72_6.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___72_6.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___72_6.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___72_6.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___72_6.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___72_6.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___72_6.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___72_6.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___72_6.FStar_TypeChecker_Env.dep_graph}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___73_12 = env
in {FStar_TypeChecker_Env.solver = uu___73_12.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___73_12.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___73_12.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___73_12.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___73_12.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___73_12.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___73_12.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___73_12.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___73_12.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___73_12.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___73_12.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___73_12.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___73_12.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___73_12.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___73_12.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___73_12.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___73_12.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___73_12.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___73_12.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___73_12.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___73_12.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___73_12.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___73_12.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___73_12.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___73_12.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___73_12.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___73_12.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___73_12.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___73_12.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___73_12.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___73_12.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___73_12.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___73_12.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___73_12.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___73_12.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___73_12.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___73_12.FStar_TypeChecker_Env.dep_graph}))


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

let uu____59 = (

let uu____68 = (FStar_Syntax_Syntax.as_arg tl1)
in (uu____68)::[])
in (uu____52)::uu____59))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____51))
in (uu____46 FStar_Pervasives_Native.None r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___66_101 -> (match (uu___66_101) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____104 -> begin
false
end))


let steps : 'Auu____111 . 'Auu____111  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[])


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
((t), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____202 -> begin
(

let t1 = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____210 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t1)
in (

let uu____214 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____214) with
| FStar_Pervasives_Native.None -> begin
((t1), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t1)
end
| uu____230 -> begin
(

let fail1 = (fun uu____240 -> (

let msg = (match (head_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____242 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" uu____242))
end
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____244 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____245 = (FStar_TypeChecker_Normalize.term_to_string env head1)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" uu____244 uu____245)))
end)
in (

let uu____246 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_EscapedBoundVar), (msg)) uu____246))))
in (

let uu____251 = (

let uu____264 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____265 = (

let uu____266 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____266))
in (FStar_TypeChecker_Util.new_implicit_var "no escape" uu____264 env uu____265)))
in (match (uu____251) with
| (s, uu____280, g0) -> begin
(

let uu____294 = (FStar_TypeChecker_Rel.try_teq true env t1 s)
in (match (uu____294) with
| FStar_Pervasives_Native.Some (g) -> begin
(

let g1 = (

let uu____303 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____303))
in ((s), (g1)))
end
| uu____304 -> begin
(fail1 ())
end))
end)))
end)
end))))
end))
in (aux false kt)))


let push_binding : 'Auu____313 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____313)  ->  FStar_TypeChecker_Env.env = (fun env b -> (FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v1 -> (

let uu____363 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____363) with
| true -> begin
s
end
| uu____364 -> begin
(FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), (v1))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags (fun uu____383 -> (

let uu____384 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Util.set_result_typ uu____384 t)))))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> e)


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____439 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____439))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____444 = (

let uu____451 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____451) with
| FStar_Pervasives_Native.None -> begin
(((memo_tk e t)), (lc), (guard))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____461 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____461) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____477 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____477) with
| (e2, g) -> begin
((

let uu____491 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____491) with
| true -> begin
(

let uu____492 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____493 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____494 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____495 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____492 uu____493 uu____494 uu____495)))))
end
| uu____496 -> begin
()
end));
(

let msg = (

let uu____503 = (FStar_TypeChecker_Rel.is_trivial g)
in (match (uu____503) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____512 -> begin
(FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____525 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc1 g1)
in (match (uu____525) with
| (lc2, g2) -> begin
(

let uu____538 = (set_lcomp_result lc2 t')
in (((memo_tk e2 t')), (uu____538), (g2)))
end))));
)
end)))
end))
end))
in (match (uu____444) with
| (e1, lc1, g) -> begin
((e1), (lc1), (g))
end)))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____575 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____575) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____585 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____585) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt ec -> (

let uu____637 = ec
in (match (uu____637) with
| (e, c) -> begin
(

let tot_or_gtot = (fun c1 -> (

let uu____660 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____660) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c1))
end
| uu____661 -> begin
(

let uu____662 = (FStar_Syntax_Util.is_pure_or_ghost_comp c1)
in (match (uu____662) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c1))
end
| uu____663 -> begin
(failwith "Impossible: Expected pure_or_ghost comp")
end))
end)))
in (

let uu____664 = (match (copt) with
| FStar_Pervasives_Native.Some (uu____677) -> begin
((copt), (c))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____680 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Parser_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____682 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____682)))))
in (match (uu____680) with
| true -> begin
(

let uu____689 = (

let uu____692 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____692))
in ((uu____689), (c)))
end
| uu____695 -> begin
(

let uu____696 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____696) with
| true -> begin
(

let uu____703 = (tot_or_gtot c)
in ((FStar_Pervasives_Native.None), (uu____703)))
end
| uu____706 -> begin
(

let uu____707 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____707) with
| true -> begin
(

let uu____714 = (

let uu____717 = (tot_or_gtot c)
in FStar_Pervasives_Native.Some (uu____717))
in ((uu____714), (c)))
end
| uu____720 -> begin
((FStar_Pervasives_Native.None), (c))
end))
end))
end))
end)
in (match (uu____664) with
| (expected_c_opt, c1) -> begin
(

let c2 = (norm_c env c1)
in (match (expected_c_opt) with
| FStar_Pervasives_Native.None -> begin
((e), (c2), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (expected_c) -> begin
(

let c3 = (

let uu____744 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e uu____744))
in (

let c4 = (FStar_Syntax_Syntax.lcomp_comp c3)
in (

let uu____746 = (FStar_TypeChecker_Util.check_comp env e c4 expected_c)
in (match (uu____746) with
| (e1, uu____760, g) -> begin
(

let g1 = (

let uu____763 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____763 "could not prove post-condition" g))
in ((

let uu____765 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____765) with
| true -> begin
(

let uu____766 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____767 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" uu____766 uu____767)))
end
| uu____768 -> begin
()
end));
(

let e2 = (FStar_TypeChecker_Util.maybe_lift env e1 (FStar_Syntax_Util.comp_effect_name c4) (FStar_Syntax_Util.comp_effect_name expected_c) (FStar_Syntax_Util.comp_result c4))
in ((e2), (expected_c), (g1)));
))
end))))
end))
end)))
end)))


let no_logical_guard : 'Auu____778 'Auu____779 . FStar_TypeChecker_Env.env  ->  ('Auu____778 * 'Auu____779 * FStar_TypeChecker_Env.guard_t)  ->  ('Auu____778 * 'Auu____779 * FStar_TypeChecker_Env.guard_t) = (fun env uu____801 -> (match (uu____801) with
| (te, kt, f) -> begin
(

let uu____811 = (FStar_TypeChecker_Rel.guard_form f)
in (match (uu____811) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____819 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____824 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____819 uu____824)))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let uu____836 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____836) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "Expected type is None\n")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____840 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____840))
end)))


let rec get_pat_vars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun pats acc -> (

let pats1 = (FStar_Syntax_Util.unmeta pats)
in (

let uu____872 = (FStar_Syntax_Util.head_and_args pats1)
in (match (uu____872) with
| (head1, args) -> begin
(

let uu____911 = (

let uu____912 = (FStar_Syntax_Util.un_uinst head1)
in uu____912.FStar_Syntax_Syntax.n)
in (match (uu____911) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
acc
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
(

let uu____919 = (FStar_List.tl args)
in (get_pat_vars_args uu____919 acc))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
(get_pat_vars_args args acc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(get_pat_vars_args args acc)
end
| uu____928 -> begin
(

let uu____929 = (FStar_Syntax_Free.names pats1)
in (FStar_Util.set_union acc uu____929))
end))
end))))
and get_pat_vars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun args acc -> (FStar_List.fold_left (fun s arg -> (get_pat_vars (FStar_Pervasives_Native.fst arg) s)) acc args))


let check_smt_pat : 'Auu____964 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * 'Auu____964) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  unit = (fun env t bs c -> (

let uu____1005 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____1005) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____1006; FStar_Syntax_Syntax.effect_name = uu____1007; FStar_Syntax_Syntax.result_typ = uu____1008; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____1012))::[]; FStar_Syntax_Syntax.flags = uu____1013}) -> begin
(

let pat_vars = (

let uu____1061 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (

let uu____1062 = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
in (get_pat_vars uu____1061 uu____1062)))
in (

let uu____1065 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____1092 -> (match (uu____1092) with
| (b, uu____1098) -> begin
(

let uu____1099 = (FStar_Util.set_mem b pat_vars)
in (not (uu____1099)))
end))))
in (match (uu____1065) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____1105) -> begin
(

let uu____1110 = (

let uu____1115 = (

let uu____1116 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____1116))
in ((FStar_Errors.Warning_PatternMissingBoundVar), (uu____1115)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1110))
end)))
end
| uu____1117 -> begin
(failwith "Impossible")
end)
end
| uu____1118 -> begin
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

let uu___74_1177 = env
in {FStar_TypeChecker_Env.solver = uu___74_1177.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___74_1177.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___74_1177.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___74_1177.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___74_1177.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___74_1177.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___74_1177.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___74_1177.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___74_1177.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___74_1177.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___74_1177.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___74_1177.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___74_1177.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___74_1177.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___74_1177.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___74_1177.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___74_1177.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___74_1177.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___74_1177.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___74_1177.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___74_1177.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___74_1177.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___74_1177.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___74_1177.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___74_1177.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___74_1177.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___74_1177.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___74_1177.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___74_1177.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___74_1177.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___74_1177.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___74_1177.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___74_1177.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___74_1177.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___74_1177.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___74_1177.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___74_1177.FStar_TypeChecker_Env.dep_graph})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> ((

let uu____1203 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1203) with
| true -> begin
(

let uu____1204 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (

let uu____1205 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "Building a decreases clause over (%s) and %s\n" uu____1204 uu____1205)))
end
| uu____1206 -> begin
()
end));
(

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____1232 -> (match (uu____1232) with
| (b, uu____1240) -> begin
(

let t = (

let uu____1242 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____1242))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____1245) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1246) -> begin
[]
end
| uu____1259 -> begin
(

let uu____1260 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____1260)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____1273 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____1273) with
| (head1, uu____1291) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____1315 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____1323 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___67_1332 -> (match (uu___67_1332) with
| FStar_Syntax_Syntax.DECREASES (uu____1333) -> begin
true
end
| uu____1336 -> begin
false
end))))
in (match (uu____1323) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____1342 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____1363 -> begin
(mk_lex_list xs)
end))
end)))));
))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____1392 -> (match (uu____1392) with
| (l, t, u_names) -> begin
(

let uu____1416 = (

let uu____1417 = (FStar_Syntax_Subst.compress t)
in uu____1417.FStar_Syntax_Syntax.n)
in (match (uu____1416) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____1466 -> (match (uu____1466) with
| (x, imp) -> begin
(

let uu____1477 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____1477) with
| true -> begin
(

let uu____1482 = (

let uu____1483 = (

let uu____1486 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____1486))
in (FStar_Syntax_Syntax.new_bv uu____1483 x.FStar_Syntax_Syntax.sort))
in ((uu____1482), (imp)))
end
| uu____1487 -> begin
((x), (imp))
end))
end))))
in (

let uu____1488 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____1488) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____1509 = (

let uu____1514 = (

let uu____1515 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____1522 = (

let uu____1531 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____1531)::[])
in (uu____1515)::uu____1522))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____1514))
in (uu____1509 FStar_Pervasives_Native.None r))
in (

let uu____1558 = (FStar_Util.prefix formals2)
in (match (uu____1558) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___75_1605 = last1
in (

let uu____1606 = (FStar_Syntax_Util.refine last1 precedes1)
in {FStar_Syntax_Syntax.ppname = uu___75_1605.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___75_1605.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1606}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____1632 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1632) with
| true -> begin
(

let uu____1633 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____1634 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1635 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____1633 uu____1634 uu____1635))))
end
| uu____1636 -> begin
()
end));
((l), (t'), (u_names));
))))
end))))
end)))
end
| uu____1639 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectedArrowAnnotatedType), ("Annotated type of \'let rec\' must be an arrow")) t.FStar_Syntax_Syntax.pos)
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let uu___76_2239 = env
in {FStar_TypeChecker_Env.solver = uu___76_2239.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___76_2239.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___76_2239.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___76_2239.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___76_2239.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___76_2239.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___76_2239.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___76_2239.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___76_2239.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___76_2239.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___76_2239.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___76_2239.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___76_2239.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___76_2239.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___76_2239.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___76_2239.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___76_2239.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___76_2239.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___76_2239.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___76_2239.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___76_2239.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___76_2239.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___76_2239.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___76_2239.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___76_2239.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___76_2239.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___76_2239.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___76_2239.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___76_2239.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___76_2239.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___76_2239.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___76_2239.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___76_2239.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___76_2239.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___76_2239.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___76_2239.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___76_2239.FStar_TypeChecker_Env.dep_graph}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (match ((Prims.op_Equality e.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____2249 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____2251 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____2251) with
| true -> begin
(

let uu____2252 = (

let uu____2253 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2253))
in (

let uu____2254 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" uu____2252 uu____2254)))
end
| uu____2255 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2263) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2294) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2301) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2302) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____2303) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2304) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____2305) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____2306) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2323) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____2336) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____2343) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____2344, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aqs}) when (FStar_List.for_all (fun uu____2372 -> (match (uu____2372) with
| (uu____2381, b, uu____2383) -> begin
(not (b))
end)) aqs) -> begin
(value_check_expected_typ env1 top (FStar_Util.Inl (FStar_Syntax_Syntax.t_term)) FStar_TypeChecker_Rel.trivial_guard)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____2388) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Tac_lid; FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_term; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.SOMETRIVIAL)::(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]})
in (

let uu____2402 = (

let uu____2409 = (

let uu____2414 = (FStar_Syntax_Util.lcomp_of_comp c)
in FStar_Util.Inr (uu____2414))
in (value_check_expected_typ env1 top uu____2409 FStar_TypeChecker_Rel.trivial_guard))
in (match (uu____2402) with
| (t, lc, g) -> begin
(

let t1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((t), (FStar_Syntax_Syntax.Meta_monadic_lift (((FStar_Parser_Const.effect_PURE_lid), (FStar_Parser_Const.effect_TAC_lid), (FStar_Syntax_Syntax.t_term))))))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in ((t1), (lc), (g)))
end)))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(value_check_expected_typ env1 top (FStar_Util.Inl (i.FStar_Syntax_Syntax.typ)) FStar_TypeChecker_Rel.trivial_guard)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____2437 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____2437) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___77_2454 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___77_2454.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___77_2454.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___77_2454.FStar_TypeChecker_Env.implicits})
in (

let uu____2455 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____2455), (c), (g1))))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____2474 = (FStar_Syntax_Util.type_u ())
in (match (uu____2474) with
| (t, u) -> begin
(

let uu____2487 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____2487) with
| (e2, c, g) -> begin
(

let uu____2503 = (

let uu____2518 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2518) with
| (env2, uu____2540) -> begin
(tc_pats env2 pats)
end))
in (match (uu____2503) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___78_2574 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___78_2574.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___78_2574.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___78_2574.FStar_TypeChecker_Env.implicits})
in (

let uu____2575 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2578 = (FStar_TypeChecker_Rel.conj_guard g g'1)
in ((uu____2575), (c), (uu____2578)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____2584 = (

let uu____2585 = (FStar_Syntax_Subst.compress e1)
in uu____2585.FStar_Syntax_Syntax.n)
in (match (uu____2584) with
| FStar_Syntax_Syntax.Tm_let ((uu____2594, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____2596; FStar_Syntax_Syntax.lbtyp = uu____2597; FStar_Syntax_Syntax.lbeff = uu____2598; FStar_Syntax_Syntax.lbdef = e11; FStar_Syntax_Syntax.lbattrs = uu____2600; FStar_Syntax_Syntax.lbpos = uu____2601})::[]), e2) -> begin
(

let uu____2629 = (

let uu____2636 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (tc_term uu____2636 e11))
in (match (uu____2629) with
| (e12, c1, g1) -> begin
(

let uu____2646 = (tc_term env1 e2)
in (match (uu____2646) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.maybe_return_e2_and_bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 e21 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e3 = (

let uu____2670 = (

let uu____2677 = (

let uu____2678 = (

let uu____2691 = (

let uu____2698 = (

let uu____2701 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_Syntax_Syntax.t_unit), (e13), (e13.FStar_Syntax_Syntax.pos)))
in (uu____2701)::[])
in ((false), (uu____2698)))
in ((uu____2691), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____2678))
in (FStar_Syntax_Syntax.mk uu____2677))
in (uu____2670 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2723 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e5), (c), (uu____2723)))))))))
end))
end))
end
| uu____2724 -> begin
(

let uu____2725 = (tc_term env1 e1)
in (match (uu____2725) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____2747)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic_lift (uu____2759)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____2778 = (tc_term env1 e1)
in (match (uu____2778) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____2802) -> begin
(

let uu____2849 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2849) with
| (env0, uu____2863) -> begin
(

let uu____2868 = (tc_comp env0 expected_c)
in (match (uu____2868) with
| (expected_c1, uu____2882, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c1)
in (

let uu____2887 = (

let uu____2894 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____2894 e1))
in (match (uu____2887) with
| (e2, c', g') -> begin
(

let uu____2904 = (

let uu____2911 = (

let uu____2916 = (FStar_Syntax_Syntax.lcomp_comp c')
in ((e2), (uu____2916)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____2911))
in (match (uu____2904) with
| (e3, expected_c2, g'') -> begin
(

let topt1 = (tc_tactic_opt env0 topt)
in (

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inr (expected_c2)), (topt1))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____2970 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____2970))
in (

let f1 = (match (topt1) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(FStar_TypeChecker_Rel.map_guard f (fun f1 -> (

let uu____2976 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero f1)
in (FStar_TypeChecker_Common.mk_by_tactic tactic uu____2976))))
end)
in (

let uu____2977 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____2977) with
| (e5, c, f2) -> begin
(

let final_guard = (FStar_TypeChecker_Rel.conj_guard f1 f2)
in ((e5), (c), (final_guard)))
end)))))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____2997) -> begin
(

let uu____3044 = (FStar_Syntax_Util.type_u ())
in (match (uu____3044) with
| (k, u) -> begin
(

let uu____3057 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____3057) with
| (t1, uu____3071, f) -> begin
(

let uu____3073 = (

let uu____3080 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____3080 e1))
in (match (uu____3073) with
| (e2, c, g) -> begin
(

let uu____3090 = (

let uu____3095 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____3100 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____3095 e2 c f))
in (match (uu____3090) with
| (c1, f1) -> begin
(

let uu____3109 = (

let uu____3116 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____3116 c1))
in (match (uu____3109) with
| (e3, c2, f2) -> begin
(

let uu____3164 = (

let uu____3165 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____3165))
in ((e3), (c2), (uu____3164)))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____3166; FStar_Syntax_Syntax.vars = uu____3167}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3230 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3230) with
| (unary_op, uu____3252) -> begin
(

let head1 = (

let uu____3276 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____3276))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____3314; FStar_Syntax_Syntax.vars = uu____3315}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3378 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3378) with
| (unary_op, uu____3400) -> begin
(

let head1 = (

let uu____3424 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____3424))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3462)); FStar_Syntax_Syntax.pos = uu____3463; FStar_Syntax_Syntax.vars = uu____3464}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3527 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3527) with
| (unary_op, uu____3549) -> begin
(

let head1 = (

let uu____3573 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____3573))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____3611; FStar_Syntax_Syntax.vars = uu____3612}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3688 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3688) with
| (unary_op, uu____3710) -> begin
(

let head1 = (

let uu____3734 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a1)::(a2)::[])))) FStar_Pervasives_Native.None uu____3734))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____3778; FStar_Syntax_Syntax.vars = uu____3779}, ((e1, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____3809 = (

let uu____3816 = (

let uu____3817 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3817))
in (tc_term uu____3816 e1))
in (match (uu____3809) with
| (e2, c, g) -> begin
(

let uu____3841 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3841) with
| (head1, uu____3863) -> begin
(

let uu____3884 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((((e2), (FStar_Pervasives_Native.None)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3909 = (

let uu____3910 = (

let uu____3911 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_Syntax_Syntax.mk_Total uu____3911))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3910))
in ((uu____3884), (uu____3909), (g))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____3912; FStar_Syntax_Syntax.vars = uu____3913}, ((t, FStar_Pervasives_Native.None))::((r, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____3954 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3954) with
| (head1, uu____3976) -> begin
(

let env' = (

let uu____3998 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_TypeChecker_Env.set_expected_typ env1 uu____3998))
in (

let uu____3999 = (tc_term env' r)
in (match (uu____3999) with
| (er, uu____4013, gr) -> begin
(

let uu____4015 = (tc_term env1 t)
in (match (uu____4015) with
| (t1, tt, gt1) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard gr gt1)
in (

let uu____4032 = (

let uu____4033 = (

let uu____4038 = (

let uu____4039 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____4046 = (

let uu____4055 = (FStar_Syntax_Syntax.as_arg r)
in (uu____4055)::[])
in (uu____4039)::uu____4046))
in (FStar_Syntax_Syntax.mk_Tm_app head1 uu____4038))
in (uu____4033 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in ((uu____4032), (tt), (g))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____4082; FStar_Syntax_Syntax.vars = uu____4083}, uu____4084) -> begin
(

let uu____4105 = (

let uu____4110 = (

let uu____4111 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____4111))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____4110)))
in (FStar_Errors.raise_error uu____4105 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____4118; FStar_Syntax_Syntax.vars = uu____4119}, uu____4120) -> begin
(

let uu____4141 = (

let uu____4146 = (

let uu____4147 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____4147))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____4146)))
in (FStar_Errors.raise_error uu____4141 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4154; FStar_Syntax_Syntax.vars = uu____4155}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify), ("Qualifier on argument to reify is irrelevant and will be ignored")))
end
| uu____4187 -> begin
()
end);
(

let uu____4188 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4188) with
| (env0, uu____4202) -> begin
(

let uu____4207 = (tc_term env0 e1)
in (match (uu____4207) with
| (e2, c, g) -> begin
(

let uu____4223 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4223) with
| (reify_op, uu____4245) -> begin
(

let u_c = (

let uu____4267 = (tc_term env0 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____4267) with
| (uu____4274, c', uu____4276) -> begin
(

let uu____4277 = (

let uu____4278 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____4278.FStar_Syntax_Syntax.n)
in (match (uu____4277) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____4282 -> begin
(

let uu____4283 = (FStar_Syntax_Util.type_u ())
in (match (uu____4283) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4295 = (

let uu____4296 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____4297 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____4298 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____4296 uu____4297 uu____4298))))
in (failwith uu____4295))
end);
u;
))
end))
end))
end))
in (

let repr = (

let uu____4300 = (FStar_Syntax_Syntax.lcomp_comp c)
in (FStar_TypeChecker_Env.reify_comp env1 uu____4300 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____4329 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____4329 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____4330 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____4330) with
| (e4, c2, g') -> begin
(

let uu____4346 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e4), (c2), (uu____4346)))
end))))))
end))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.pos = uu____4348; FStar_Syntax_Syntax.vars = uu____4349}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect), ("Qualifier on argument to reflect is irrelevant and will be ignored")))
end
| uu____4381 -> begin
()
end);
(

let no_reflect = (fun uu____4393 -> (

let uu____4394 = (

let uu____4399 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____4399)))
in (FStar_Errors.raise_error uu____4394 e1.FStar_Syntax_Syntax.pos)))
in (

let uu____4406 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4406) with
| (reflect_op, uu____4428) -> begin
(

let uu____4449 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____4449) with
| FStar_Pervasives_Native.None -> begin
(no_reflect ())
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____4482 = (

let uu____4483 = (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____4483)))
in (match (uu____4482) with
| true -> begin
(no_reflect ())
end
| uu____4492 -> begin
(

let uu____4493 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4493) with
| (env_no_ex, topt) -> begin
(

let uu____4512 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____4534 = (

let uu____4541 = (

let uu____4542 = (

let uu____4557 = (

let uu____4566 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____4573 = (

let uu____4582 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____4582)::[])
in (uu____4566)::uu____4573))
in ((repr), (uu____4557)))
in FStar_Syntax_Syntax.Tm_app (uu____4542))
in (FStar_Syntax_Syntax.mk uu____4541))
in (uu____4534 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____4620 = (

let uu____4627 = (

let uu____4628 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____4628 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____4627 t))
in (match (uu____4620) with
| (t1, uu____4656, g) -> begin
(

let uu____4658 = (

let uu____4659 = (FStar_Syntax_Subst.compress t1)
in uu____4659.FStar_Syntax_Syntax.n)
in (match (uu____4658) with
| FStar_Syntax_Syntax.Tm_app (uu____4674, ((res, uu____4676))::((wp, uu____4678))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____4721 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____4512) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____4752 = (

let uu____4757 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____4757) with
| (e2, c, g) -> begin
((

let uu____4772 = (

let uu____4773 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____4773))
in (match (uu____4772) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 ((((FStar_Errors.Error_UnexpectedGTotComputation), ("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____4786 -> begin
()
end));
(

let uu____4787 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____4787) with
| FStar_Pervasives_Native.None -> begin
((

let uu____4795 = (

let uu____4804 = (

let uu____4811 = (

let uu____4812 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____4813 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____4812 uu____4813)))
in ((FStar_Errors.Error_UnexpectedInstance), (uu____4811), (e2.FStar_Syntax_Syntax.pos)))
in (uu____4804)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____4795));
(

let uu____4826 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e2), (uu____4826)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____4828 = (

let uu____4829 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____4829))
in ((e2), (uu____4828)))
end));
)
end))
in (match (uu____4752) with
| (e2, g) -> begin
(

let c = (

let uu____4839 = (

let uu____4840 = (

let uu____4841 = (

let uu____4842 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____4842)::[])
in (

let uu____4843 = (

let uu____4852 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4852)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____4841; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____4843; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____4840))
in (FStar_All.pipe_right uu____4839 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____4898 = (comp_check_expected_typ env1 e3 c)
in (match (uu____4898) with
| (e4, c1, g') -> begin
(

let uu____4914 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e4), (c1), (uu____4914)))
end))))
end))
end))
end))
end))
end))
end)));
)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) when (FStar_Syntax_Util.is_synth_by_tactic head1) -> begin
(tc_synth env1 args top.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let env0 = env1
in (

let env2 = (

let uu____4961 = (

let uu____4962 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____4962 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____4961 instantiate_both))
in ((

let uu____4978 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____4978) with
| true -> begin
(

let uu____4979 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____4980 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____4981 = (

let uu____4982 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right uu____4982 (fun uu___68_4988 -> (match (uu___68_4988) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) Checking app %s, expected type is %s\n" uu____4979 uu____4980 uu____4981))))
end
| uu____4992 -> begin
()
end));
(

let uu____4993 = (tc_term (no_inst env2) head1)
in (match (uu____4993) with
| (head2, chead, g_head) -> begin
(

let uu____5009 = (

let uu____5016 = (((not (env2.FStar_TypeChecker_Env.lax)) && (

let uu____5018 = (FStar_Options.lax ())
in (not (uu____5018)))) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____5016) with
| true -> begin
(

let uu____5025 = (

let uu____5032 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____5032))
in (match (uu____5025) with
| (e1, c, g) -> begin
((e1), (c), (g))
end))
end
| uu____5044 -> begin
(

let uu____5045 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env2 head2 chead g_head args uu____5045))
end))
in (match (uu____5009) with
| (e1, c, g) -> begin
((

let uu____5058 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____5058) with
| true -> begin
(

let uu____5059 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____5059))
end
| uu____5060 -> begin
()
end));
(

let uu____5061 = (comp_check_expected_typ env0 e1 c)
in (match (uu____5061) with
| (e2, c1, g') -> begin
(

let gres = (FStar_TypeChecker_Rel.conj_guard g g')
in ((

let uu____5079 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____5079) with
| true -> begin
(

let uu____5080 = (FStar_Syntax_Print.term_to_string e2)
in (

let uu____5081 = (FStar_TypeChecker_Rel.guard_to_string env2 gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____5080 uu____5081)))
end
| uu____5082 -> begin
()
end));
((e2), (c1), (gres));
))
end));
)
end))
end));
)))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let uu____5121 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5121) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____5141 = (tc_term env12 e1)
in (match (uu____5141) with
| (e11, c1, g1) -> begin
(

let uu____5157 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t), (g1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5171 = (FStar_Syntax_Util.type_u ())
in (match (uu____5171) with
| (k, uu____5183) -> begin
(

let uu____5184 = (FStar_TypeChecker_Util.new_implicit_var "match result" e.FStar_Syntax_Syntax.pos env1 k)
in (match (uu____5184) with
| (res_t, uu____5204, g) -> begin
(

let uu____5218 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in (

let uu____5219 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in ((uu____5218), (res_t), (uu____5219))))
end))
end))
end)
in (match (uu____5157) with
| (env_branches, res_t, g11) -> begin
((

let uu____5230 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____5230) with
| true -> begin
(

let uu____5231 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____5231))
end
| uu____5232 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____5352 = (

let uu____5357 = (FStar_List.fold_right (fun uu____5436 uu____5437 -> (match (((uu____5436), (uu____5437))) with
| ((branch1, f, eff_label, cflags, c, g), (caccum, gaccum)) -> begin
(

let uu____5671 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (eff_label), (cflags), (c)))::caccum), (uu____5671)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____5357) with
| (cases, g) -> begin
(

let uu____5769 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____5769), (g)))
end))
in (match (uu____5352) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____5911 -> (match (uu____5911) with
| ((pat, wopt, br), uu____5955, eff_label, uu____5957, uu____5958, uu____5959) -> begin
(

let uu____5994 = (FStar_TypeChecker_Util.maybe_lift env1 br eff_label cres.FStar_Syntax_Syntax.eff_name res_t)
in ((pat), (wopt), (uu____5994)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____6061 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____6061) with
| true -> begin
(mk_match e11)
end
| uu____6064 -> begin
(

let e_match = (

let uu____6068 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____6068))
in (

let lb = (

let uu____6072 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (guard_x)) [] c1.FStar_Syntax_Syntax.res_typ uu____6072 e11 [] e11.FStar_Syntax_Syntax.pos))
in (

let e2 = (

let uu____6078 = (

let uu____6085 = (

let uu____6086 = (

let uu____6099 = (

let uu____6102 = (

let uu____6103 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____6103)::[])
in (FStar_Syntax_Subst.close uu____6102 e_match))
in ((((false), ((lb)::[]))), (uu____6099)))
in FStar_Syntax_Syntax.Tm_let (uu____6086))
in (FStar_Syntax_Syntax.mk uu____6085))
in (uu____6078 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____6130 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____6130) with
| true -> begin
(

let uu____6131 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____6132 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____6131 uu____6132)))
end
| uu____6133 -> begin
()
end));
(

let uu____6134 = (FStar_TypeChecker_Rel.conj_guard g11 g_branches)
in ((e2), (cres), (uu____6134)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____6135); FStar_Syntax_Syntax.lbunivs = uu____6136; FStar_Syntax_Syntax.lbtyp = uu____6137; FStar_Syntax_Syntax.lbeff = uu____6138; FStar_Syntax_Syntax.lbdef = uu____6139; FStar_Syntax_Syntax.lbattrs = uu____6140; FStar_Syntax_Syntax.lbpos = uu____6141})::[]), uu____6142) -> begin
(check_top_level_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____6165), uu____6166) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____6181); FStar_Syntax_Syntax.lbunivs = uu____6182; FStar_Syntax_Syntax.lbtyp = uu____6183; FStar_Syntax_Syntax.lbeff = uu____6184; FStar_Syntax_Syntax.lbdef = uu____6185; FStar_Syntax_Syntax.lbattrs = uu____6186; FStar_Syntax_Syntax.lbpos = uu____6187})::uu____6188), uu____6189) -> begin
(check_top_level_let_rec env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____6214), uu____6215) -> begin
(check_inner_let_rec env1 top)
end));
)))
and tc_synth : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env args rng -> (

let uu____6241 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.None), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6311))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.Some (a)), (rest))
end
| uu____6358 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: bad application")) rng)
end)
in (match (uu____6241) with
| (tau, atyp, rest) -> begin
(

let typ = (match (atyp) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6420 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6420) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6424 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: need a type annotation when no expected type is present")) uu____6424))
end))
end)
in (

let uu____6425 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____6425) with
| (env', uu____6439) -> begin
(

let uu____6444 = (tc_term env' typ)
in (match (uu____6444) with
| (typ1, uu____6458, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g1);
(

let uu____6461 = (tc_tactic env' tau)
in (match (uu____6461) with
| (tau1, uu____6475, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g2);
(

let t = (match (env.FStar_TypeChecker_Env.nosynth) with
| true -> begin
(

let uu____6483 = (

let uu____6488 = (FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.magic_lid)
in (

let uu____6489 = (

let uu____6490 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____6490)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____6488 uu____6489)))
in (uu____6483 FStar_Pervasives_Native.None rng))
end
| uu____6511 -> begin
(

let t = (env.FStar_TypeChecker_Env.synth_hook env' typ1 tau1)
in ((

let uu____6514 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____6514) with
| true -> begin
(

let uu____6515 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____6515))
end
| uu____6516 -> begin
()
end));
t;
))
end)
in ((FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(

let uu____6518 = (FStar_Syntax_Syntax.mk_Tm_app t rest FStar_Pervasives_Native.None rng)
in (tc_term env uu____6518));
));
)
end));
)
end))
end)))
end)))
and tc_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___79_6522 = env
in {FStar_TypeChecker_Env.solver = uu___79_6522.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___79_6522.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___79_6522.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___79_6522.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___79_6522.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___79_6522.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___79_6522.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___79_6522.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___79_6522.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___79_6522.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___79_6522.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___79_6522.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___79_6522.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___79_6522.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___79_6522.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___79_6522.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___79_6522.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___79_6522.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___79_6522.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___79_6522.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___79_6522.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___79_6522.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___79_6522.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___79_6522.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___79_6522.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___79_6522.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___79_6522.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___79_6522.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___79_6522.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___79_6522.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___79_6522.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___79_6522.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___79_6522.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___79_6522.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___79_6522.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___79_6522.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___79_6522.FStar_TypeChecker_Env.dep_graph})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit)))
and tc_reified_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___80_6526 = env
in {FStar_TypeChecker_Env.solver = uu___80_6526.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___80_6526.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___80_6526.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___80_6526.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___80_6526.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___80_6526.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___80_6526.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___80_6526.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___80_6526.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___80_6526.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___80_6526.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___80_6526.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___80_6526.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___80_6526.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___80_6526.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___80_6526.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___80_6526.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___80_6526.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___80_6526.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___80_6526.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___80_6526.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___80_6526.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___80_6526.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___80_6526.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___80_6526.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___80_6526.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___80_6526.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___80_6526.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___80_6526.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___80_6526.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___80_6526.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___80_6526.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___80_6526.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___80_6526.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___80_6526.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___80_6526.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___80_6526.FStar_TypeChecker_Env.dep_graph})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____6542 = (tc_tactic env tactic)
in (match (uu____6542) with
| (tactic1, uu____6552, uu____6553) -> begin
FStar_Pervasives_Native.Some (tactic1)
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t0 -> (

let uu____6602 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0)
in (match (uu____6602) with
| (e2, t, implicits) -> begin
(

let tc = (

let uu____6623 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____6623) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____6628 -> begin
(

let uu____6629 = (

let uu____6630 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6630))
in FStar_Util.Inr (uu____6629))
end))
in (

let is_data_ctor = (fun uu___69_6638 -> (match (uu___69_6638) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6641)) -> begin
true
end
| uu____6648 -> begin
false
end))
in (

let uu____6651 = ((is_data_ctor dc) && (

let uu____6653 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____6653))))
in (match (uu____6651) with
| true -> begin
(

let uu____6660 = (

let uu____6665 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingDataConstructor), (uu____6665)))
in (

let uu____6666 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____6660 uu____6666)))
end
| uu____6673 -> begin
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

let uu____6683 = (

let uu____6684 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____6684))
in (failwith uu____6683))
end
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
(value_check_expected_typ env1 e (FStar_Util.Inl (u.FStar_Syntax_Syntax.ctx_uvar_typ)) FStar_TypeChecker_Rel.trivial_guard)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____6693 = (

let uu____6706 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____6706) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6721 = (FStar_Syntax_Util.type_u ())
in (match (uu____6721) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____6693) with
| (t, uu____6758, g0) -> begin
(

let uu____6772 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____6772) with
| (e1, uu____6792, g1) -> begin
(

let uu____6806 = (

let uu____6807 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____6807 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____6808 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e1), (uu____6806), (uu____6808))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____6810 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____6819 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____6819)))
end
| uu____6820 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____6810) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___81_6832 = x
in {FStar_Syntax_Syntax.ppname = uu___81_6832.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___81_6832.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Env.insert_bv_info env1 x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____6835 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____6835) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____6856 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____6856) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____6861 -> begin
(

let uu____6862 = (

let uu____6863 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6863))
in FStar_Util.Inr (uu____6862))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6865; FStar_Syntax_Syntax.vars = uu____6866}, uu____6867) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____6872 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____6872))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____6880 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____6880))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6888; FStar_Syntax_Syntax.vars = uu____6889}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____6898 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6898) with
| ((us', t), range) -> begin
((match ((Prims.op_disEquality (FStar_List.length us1) (FStar_List.length us'))) with
| true -> begin
(

let uu____6921 = (

let uu____6926 = (

let uu____6927 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____6928 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____6929 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____6927 uu____6928 uu____6929))))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____6926)))
in (

let uu____6930 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____6921 uu____6930)))
end
| uu____6931 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____6946 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____6950 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6950 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____6952 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6952) with
| ((us, t), range) -> begin
((

let uu____6975 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____6975) with
| true -> begin
(

let uu____6976 = (

let uu____6977 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____6977))
in (

let uu____6978 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____6979 = (FStar_Range.string_of_range range)
in (

let uu____6980 = (FStar_Range.string_of_use_range range)
in (

let uu____6981 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____6976 uu____6978 uu____6979 uu____6980 uu____6981))))))
end
| uu____6982 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____6986 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6986 us))
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
in (value_check_expected_typ env1 e1 (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7010 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7010) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____7024 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____7024) with
| (env2, uu____7038) -> begin
(

let uu____7043 = (tc_binders env2 bs1)
in (match (uu____7043) with
| (bs2, env3, g, us) -> begin
(

let uu____7062 = (tc_comp env3 c1)
in (match (uu____7062) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___82_7081 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___82_7081.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___82_7081.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____7090 = (FStar_TypeChecker_Rel.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Rel.conj_guard g uu____7090))
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
in (value_check_expected_typ env1 e1 (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____7106 = (

let uu____7111 = (

let uu____7112 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____7112)::[])
in (FStar_Syntax_Subst.open_term uu____7111 phi))
in (match (uu____7106) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____7134 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____7134) with
| (env2, uu____7148) -> begin
(

let uu____7153 = (

let uu____7166 = (FStar_List.hd x1)
in (tc_binder env2 uu____7166))
in (match (uu____7153) with
| (x2, env3, f1, u) -> begin
((

let uu____7194 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____7194) with
| true -> begin
(

let uu____7195 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____7196 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____7197 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____7195 uu____7196 uu____7197))))
end
| uu____7198 -> begin
()
end));
(

let uu____7199 = (FStar_Syntax_Util.type_u ())
in (match (uu____7199) with
| (t_phi, uu____7211) -> begin
(

let uu____7212 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____7212) with
| (phi2, uu____7226, f2) -> begin
(

let e1 = (

let uu___83_7231 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___83_7231.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___83_7231.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____7238 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____7238))
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____7258) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____7281 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____7281) with
| true -> begin
(

let uu____7282 = (FStar_Syntax_Print.term_to_string (

let uu___84_7285 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.pos = uu___84_7285.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___84_7285.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____7282))
end
| uu____7296 -> begin
()
end));
(

let uu____7297 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____7297) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____7310 -> begin
(

let uu____7311 = (

let uu____7312 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____7313 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____7312 uu____7313)))
in (failwith uu____7311))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Syntax_Syntax.t_unit
end
| FStar_Const.Const_bool (uu____7323) -> begin
FStar_Syntax_Util.t_bool
end
| FStar_Const.Const_int (uu____7324, FStar_Pervasives_Native.None) -> begin
FStar_Syntax_Syntax.t_int
end
| FStar_Const.Const_int (uu____7335, FStar_Pervasives_Native.Some (msize)) -> begin
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
| FStar_Const.Const_string (uu____7351) -> begin
FStar_Syntax_Syntax.t_string
end
| FStar_Const.Const_float (uu____7356) -> begin
FStar_Syntax_Syntax.t_float
end
| FStar_Const.Const_char (uu____7357) -> begin
(

let uu____7358 = (

let uu____7363 = (FStar_Syntax_DsEnv.try_lookup_lid env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid)
in (FStar_All.pipe_right uu____7363 FStar_Util.must))
in (FStar_All.pipe_right uu____7358 FStar_Pervasives_Native.fst))
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____7388) -> begin
FStar_Syntax_Syntax.t_range
end
| FStar_Const.Const_range_of -> begin
(

let uu____7389 = (

let uu____7394 = (

let uu____7395 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7395))
in ((FStar_Errors.Fatal_IllTyped), (uu____7394)))
in (FStar_Errors.raise_error uu____7389 r))
end
| FStar_Const.Const_set_range_of -> begin
(

let uu____7396 = (

let uu____7401 = (

let uu____7402 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7402))
in ((FStar_Errors.Fatal_IllTyped), (uu____7401)))
in (FStar_Errors.raise_error uu____7396 r))
end
| FStar_Const.Const_reify -> begin
(

let uu____7403 = (

let uu____7408 = (

let uu____7409 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7409))
in ((FStar_Errors.Fatal_IllTyped), (uu____7408)))
in (FStar_Errors.raise_error uu____7403 r))
end
| FStar_Const.Const_reflect (uu____7410) -> begin
(

let uu____7411 = (

let uu____7416 = (

let uu____7417 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7417))
in ((FStar_Errors.Fatal_IllTyped), (uu____7416)))
in (FStar_Errors.raise_error uu____7411 r))
end
| uu____7418 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedConstant), ("Unsupported constant")) r)
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____7435) -> begin
(

let uu____7444 = (FStar_Syntax_Util.type_u ())
in (match (uu____7444) with
| (k, u) -> begin
(

let uu____7457 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____7457) with
| (t1, uu____7471, g) -> begin
(

let uu____7473 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____7473), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____7475) -> begin
(

let uu____7484 = (FStar_Syntax_Util.type_u ())
in (match (uu____7484) with
| (k, u) -> begin
(

let uu____7497 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____7497) with
| (t1, uu____7511, g) -> begin
(

let uu____7513 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____7513), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let head1 = (FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
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

let uu____7523 = (

let uu____7528 = (

let uu____7529 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____7529)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____7528))
in (uu____7523 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____7544 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____7544) with
| (tc1, uu____7558, f) -> begin
(

let uu____7560 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____7560) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____7604 = (

let uu____7605 = (FStar_Syntax_Subst.compress head3)
in uu____7605.FStar_Syntax_Syntax.n)
in (match (uu____7604) with
| FStar_Syntax_Syntax.Tm_uinst (uu____7608, us) -> begin
us
end
| uu____7614 -> begin
[]
end))
in (

let uu____7615 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____7615) with
| (uu____7636, args1) -> begin
(

let uu____7658 = (

let uu____7675 = (FStar_List.hd args1)
in (

let uu____7686 = (FStar_List.tl args1)
in ((uu____7675), (uu____7686))))
in (match (uu____7658) with
| (res, args2) -> begin
(

let uu____7745 = (

let uu____7754 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___70_7782 -> (match (uu___70_7782) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____7790 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____7790) with
| (env1, uu____7802) -> begin
(

let uu____7807 = (tc_tot_or_gtot_term env1 e)
in (match (uu____7807) with
| (e1, uu____7819, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____7754 FStar_List.unzip))
in (match (uu____7745) with
| (flags1, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___85_7856 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___85_7856.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___85_7856.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____7860 = (FStar_TypeChecker_Env.effect_repr env c2 u)
in (match (uu____7860) with
| FStar_Pervasives_Native.None -> begin
u
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____7864 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c2), (u_c), (uu____7864))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____7874) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____7875) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____7885 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____7885))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____7889 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____7889))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(

let uu____7893 = (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x))
in (match (uu____7893) with
| true -> begin
u2
end
| uu____7894 -> begin
(

let uu____7895 = (

let uu____7896 = (

let uu____7897 = (FStar_Syntax_Print.univ_to_string u2)
in (Prims.strcat uu____7897 " not found"))
in (Prims.strcat "Universe variable " uu____7896))
in (failwith uu____7895))
end))
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____7898 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____7899 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7899 FStar_Pervasives_Native.snd))
end
| uu____7908 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail1 = (fun msg t -> (

let uu____7937 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in (FStar_Errors.raise_error uu____7937 top.FStar_Syntax_Syntax.pos)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____8055 bs2 bs_expected1 -> (match (uu____8055) with
| (env2, out, g, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.None), (g), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((match (((imp), (imp'))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8287))) -> begin
(

let uu____8292 = (

let uu____8297 = (

let uu____8298 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____8298))
in ((FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation), (uu____8297)))
in (

let uu____8299 = (FStar_Syntax_Syntax.range_of_bv hd1)
in (FStar_Errors.raise_error uu____8292 uu____8299)))
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8300)), FStar_Pervasives_Native.None) -> begin
(

let uu____8305 = (

let uu____8310 = (

let uu____8311 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____8311))
in ((FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation), (uu____8310)))
in (

let uu____8312 = (FStar_Syntax_Syntax.range_of_bv hd1)
in (FStar_Errors.raise_error uu____8305 uu____8312)))
end
| uu____8313 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____8323 = (

let uu____8328 = (

let uu____8329 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____8329.FStar_Syntax_Syntax.n)
in (match (uu____8328) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____8336 -> begin
((

let uu____8338 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____8338) with
| true -> begin
(

let uu____8339 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____8339))
end
| uu____8340 -> begin
()
end));
(

let uu____8341 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____8341) with
| (t, uu____8353, g1) -> begin
(

let g2 = (

let uu____8356 = (FStar_TypeChecker_Rel.teq_nosmt env2 t expected_t)
in (match (uu____8356) with
| true -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____8357 -> begin
(

let uu____8358 = (FStar_TypeChecker_Rel.get_subtyping_prop env2 expected_t t)
in (match (uu____8358) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8361 = (FStar_TypeChecker_Err.basic_type_error env2 FStar_Pervasives_Native.None expected_t t)
in (

let uu____8366 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____8361 uu____8366)))
end
| FStar_Pervasives_Native.Some (g2) -> begin
(

let uu____8368 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_TypeChecker_Util.label_guard uu____8368 "Type annotation on parameter incompatible with the expected type" g2))
end))
end))
in (

let g3 = (

let uu____8370 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____8370))
in ((t), (g3))))
end));
)
end))
in (match (uu____8323) with
| (t, g1) -> begin
(

let hd2 = (

let uu___86_8410 = hd1
in {FStar_Syntax_Syntax.ppname = uu___86_8410.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___86_8410.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env3 = (push_binding env2 b)
in (

let subst2 = (

let uu____8423 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____8423))
in (aux ((env3), ((b)::out), (g1), (subst2)) bs3 bs_expected2))))))
end)));
)
end
| (rest, []) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.Some (FStar_Util.Inl (rest))), (g), (subst1))
end
| ([], rest) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.Some (FStar_Util.Inr (rest))), (g), (subst1))
end)
end))
in (aux ((env1), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs1 bs_expected)))
in (

let rec expected_function_typ1 = (fun env1 t0 body1 -> (match (t0) with
| FStar_Pervasives_Native.None -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____8675 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____8684 = (tc_binders env1 bs)
in (match (uu____8684) with
| (bs1, envbody, g, uu____8714) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody), (body1), (g))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____8756 = (

let uu____8757 = (FStar_Syntax_Subst.compress t2)
in uu____8757.FStar_Syntax_Syntax.n)
in (match (uu____8756) with
| FStar_Syntax_Syntax.Tm_uvar (uu____8780) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____8788 -> begin
(failwith "Impossible")
end);
(

let uu____8797 = (tc_binders env1 bs)
in (match (uu____8797) with
| (bs1, envbody, g, uu____8829) -> begin
(

let uu____8830 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____8830) with
| (envbody1, uu____8858) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____8869); FStar_Syntax_Syntax.pos = uu____8870; FStar_Syntax_Syntax.vars = uu____8871}, uu____8872) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____8900 -> begin
(failwith "Impossible")
end);
(

let uu____8909 = (tc_binders env1 bs)
in (match (uu____8909) with
| (bs1, envbody, g, uu____8941) -> begin
(

let uu____8942 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____8942) with
| (envbody1, uu____8970) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____8982) -> begin
(

let uu____8987 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____8987) with
| (uu____9028, bs1, bs', copt, env2, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), (bs'), (copt), (env2), (body2), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____9071 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____9071) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 body2 -> (

let rec handle_more = (fun uu____9200 c_expected2 body3 -> (match (uu____9200) with
| (env3, bs2, more, guard, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9304 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env3), (bs2), (guard), (uu____9304), (body3)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____9319 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____9319))
in (

let uu____9320 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env3), (bs2), (guard), (uu____9320), (body3))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (

let uu____9335 = ((FStar_Options.ml_ish ()) || (FStar_Syntax_Util.is_named_tot c))
in (match (uu____9335) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env3 (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____9391 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____9391) with
| (bs_expected4, c_expected4) -> begin
(

let uu____9416 = (check_binders env3 more_bs bs_expected4)
in (match (uu____9416) with
| (env4, bs', more1, guard', subst2) -> begin
(

let uu____9468 = (

let uu____9493 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env4), ((FStar_List.append bs2 bs')), (more1), (uu____9493), (subst2)))
in (handle_more uu____9468 c_expected4 body3))
end))
end))
end
| uu____9512 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env3), (bs2), (guard), (c), (body4)))
end))
end
| uu____9524 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env3), (bs2), (guard), (c), (body4)))
end)))
end)
end))
in (

let uu____9536 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____9536 c_expected1 body2))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___87_9597 = envbody
in {FStar_TypeChecker_Env.solver = uu___87_9597.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___87_9597.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___87_9597.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___87_9597.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___87_9597.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___87_9597.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___87_9597.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___87_9597.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___87_9597.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___87_9597.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___87_9597.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___87_9597.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___87_9597.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___87_9597.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___87_9597.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___87_9597.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___87_9597.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___87_9597.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___87_9597.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___87_9597.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___87_9597.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___87_9597.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___87_9597.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___87_9597.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___87_9597.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___87_9597.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___87_9597.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___87_9597.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___87_9597.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___87_9597.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___87_9597.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___87_9597.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___87_9597.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___87_9597.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___87_9597.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___87_9597.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___87_9597.FStar_TypeChecker_Env.dep_graph})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____9655 uu____9656 -> (match (((uu____9655), (uu____9656))) with
| ((env2, letrec_binders), (l, t3, u_names)) -> begin
(

let uu____9738 = (

let uu____9745 = (

let uu____9746 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____9746 FStar_Pervasives_Native.fst))
in (tc_term uu____9745 t3))
in (match (uu____9738) with
| (t4, uu____9768, uu____9769) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l ((u_names), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____9781 = (FStar_Syntax_Syntax.mk_binder (

let uu___88_9784 = x
in {FStar_Syntax_Syntax.ppname = uu___88_9784.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___88_9784.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____9781)::letrec_binders)
end
| uu____9785 -> begin
letrec_binders
end)
in ((env3), (lb))))
end))
end)) ((envbody1), ([])))))))
in (

let uu____9794 = (check_actuals_against_formals env1 bs bs_expected1 body1)
in (match (uu____9794) with
| (envbody, bs1, g, c, body2) -> begin
(

let uu____9854 = (mk_letrec_env envbody bs1 c)
in (match (uu____9854) with
| (envbody1, letrecs) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in ((FStar_Pervasives_Native.Some (t2)), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (envbody2), (body2), (g)))
end))
end))))
end))
end
| uu____9894 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____9915 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____9915))
end
| uu____9916 -> begin
(

let uu____9917 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____9917) with
| (uu____9956, bs1, uu____9958, c_opt, envbody, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (c_opt), (envbody), (body2), (g))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____9978 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9978) with
| (env1, topt) -> begin
((

let uu____9998 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____9998) with
| true -> begin
(

let uu____9999 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____9999 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____10001 -> begin
"false"
end)))
end
| uu____10002 -> begin
()
end));
(

let uu____10003 = (expected_function_typ1 env1 topt body)
in (match (uu____10003) with
| (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1, g) -> begin
(

let uu____10043 = (

let should_check_expected_effect = (

let uu____10051 = (

let uu____10058 = (

let uu____10059 = (FStar_Syntax_Subst.compress body1)
in uu____10059.FStar_Syntax_Syntax.n)
in ((c_opt), (uu____10058)))
in (match (uu____10051) with
| (FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Tm_ascribed (uu____10064, (FStar_Util.Inr (expected_c), uu____10066), uu____10067)) -> begin
false
end
| uu____10116 -> begin
true
end))
in (

let uu____10123 = (tc_term (

let uu___89_10132 = envbody
in {FStar_TypeChecker_Env.solver = uu___89_10132.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___89_10132.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___89_10132.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___89_10132.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___89_10132.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___89_10132.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___89_10132.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___89_10132.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___89_10132.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___89_10132.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___89_10132.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___89_10132.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___89_10132.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___89_10132.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___89_10132.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___89_10132.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___89_10132.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___89_10132.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___89_10132.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___89_10132.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___89_10132.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___89_10132.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___89_10132.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___89_10132.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___89_10132.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___89_10132.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___89_10132.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___89_10132.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___89_10132.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___89_10132.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___89_10132.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___89_10132.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___89_10132.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___89_10132.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___89_10132.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___89_10132.FStar_TypeChecker_Env.dep_graph}) body1)
in (match (uu____10123) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (match (should_check_expected_effect) with
| true -> begin
(

let uu____10149 = (

let uu____10156 = (

let uu____10161 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____10161)))
in (check_expected_effect (

let uu___90_10164 = envbody
in {FStar_TypeChecker_Env.solver = uu___90_10164.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___90_10164.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___90_10164.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___90_10164.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___90_10164.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___90_10164.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___90_10164.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___90_10164.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___90_10164.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___90_10164.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___90_10164.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___90_10164.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___90_10164.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___90_10164.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___90_10164.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___90_10164.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___90_10164.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___90_10164.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___90_10164.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___90_10164.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___90_10164.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___90_10164.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___90_10164.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___90_10164.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___90_10164.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___90_10164.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___90_10164.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___90_10164.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___90_10164.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___90_10164.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___90_10164.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___90_10164.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___90_10164.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___90_10164.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___90_10164.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___90_10164.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___90_10164.FStar_TypeChecker_Env.dep_graph}) c_opt uu____10156))
in (match (uu____10149) with
| (body3, cbody1, guard) -> begin
(

let uu____10174 = (FStar_TypeChecker_Rel.conj_guard guard_body1 guard)
in ((body3), (cbody1), (uu____10174)))
end))
end
| uu____10175 -> begin
(

let uu____10176 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____10176), (guard_body1)))
end))
end)))
in (match (uu____10043) with
| (body2, cbody, guard) -> begin
(

let guard1 = (

let uu____10187 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____10189 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____10189))))
in (match (uu____10187) with
| true -> begin
(

let uu____10190 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____10190))
end
| uu____10191 -> begin
(

let guard1 = (

let uu____10193 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard env1 (FStar_List.append bs1 letrec_binders) uu____10193))
in guard1)
end))
in (

let guard2 = (FStar_TypeChecker_Util.close_guard_implicits env1 bs1 guard1)
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody)
in (

let e = (FStar_Syntax_Util.abs bs1 body2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody c_opt)))))
in (

let uu____10205 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____10232) -> begin
((e), (t1), (guard2))
end
| uu____10247 -> begin
(

let uu____10248 = (FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
in (match (uu____10248) with
| (e1, guard') -> begin
(

let uu____10263 = (FStar_TypeChecker_Rel.conj_guard guard2 guard')
in ((e1), (t1), (uu____10263)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard2))
end)
in (match (uu____10205) with
| (e1, tfun, guard3) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Total tfun)
in (

let uu____10280 = (

let uu____10285 = (FStar_Syntax_Util.lcomp_of_comp c)
in (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 uu____10285 guard3))
in (match (uu____10280) with
| (c1, g1) -> begin
((e1), (c1), (g1))
end)))
end))))))
end))
end));
)
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head1 chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in ((

let uu____10331 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____10331) with
| true -> begin
(

let uu____10332 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____10333 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____10332 uu____10333)))
end
| uu____10334 -> begin
()
end));
(

let monadic_application = (fun uu____10406 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____10406) with
| (head2, chead1, ghead1, cres) -> begin
(

let uu____10469 = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____10469) with
| (rt, g0) -> begin
(

let cres1 = (

let uu___91_10483 = cres
in {FStar_Syntax_Syntax.eff_name = uu___91_10483.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___91_10483.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___91_10483.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____10484 = (match (bs) with
| [] -> begin
(

let g = (

let uu____10498 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.conj_guard g0) uu____10498))
in ((cres1), (g)))
end
| uu____10499 -> begin
(

let g = (

let uu____10507 = (

let uu____10508 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____10508 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (FStar_TypeChecker_Rel.conj_guard g0 uu____10507))
in (

let uu____10509 = (

let uu____10510 = (

let uu____10511 = (

let uu____10512 = (FStar_Syntax_Syntax.lcomp_comp cres1)
in (FStar_Syntax_Util.arrow bs uu____10512))
in (FStar_Syntax_Syntax.mk_Total uu____10511))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____10510))
in ((uu____10509), (g))))
end)
in (match (uu____10484) with
| (cres2, guard1) -> begin
((

let uu____10524 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____10524) with
| true -> begin
(

let uu____10525 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____10525))
end
| uu____10526 -> begin
()
end));
(

let cres3 = (

let head_is_pure_and_some_arg_is_effectful = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1) && (FStar_Util.for_some (fun uu____10541 -> (match (uu____10541) with
| (uu____10550, uu____10551, lc) -> begin
((

let uu____10559 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____10559))) || (FStar_TypeChecker_Util.should_not_inline_lc lc))
end)) arg_comps_rev))
in (

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (

let uu____10569 = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2) && head_is_pure_and_some_arg_is_effectful)
in (match (uu____10569) with
| true -> begin
((

let uu____10571 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10571) with
| true -> begin
(

let uu____10572 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: Return inserted in monadic application: %s\n" uu____10572))
end
| uu____10573 -> begin
()
end));
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2);
)
end
| uu____10574 -> begin
((

let uu____10576 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10576) with
| true -> begin
(

let uu____10577 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: No return inserted in monadic application: %s\n" uu____10577))
end
| uu____10578 -> begin
()
end));
cres2;
)
end))))
in (

let comp = (FStar_List.fold_left (fun out_c uu____10603 -> (match (uu____10603) with
| ((e, q), x, c) -> begin
((

let uu____10637 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10637) with
| true -> begin
(

let uu____10638 = (match (x) with
| FStar_Pervasives_Native.None -> begin
"_"
end
| FStar_Pervasives_Native.Some (x1) -> begin
(FStar_Syntax_Print.bv_to_string x1)
end)
in (

let uu____10640 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print2 "(b) Monadic app: Binding argument %s : %s\n" uu____10638 uu____10640)))
end
| uu____10641 -> begin
()
end));
(

let uu____10642 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____10642) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____10645 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end));
)
end)) cres3 arg_comps_rev)
in (

let comp1 = ((

let uu____10650 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10650) with
| true -> begin
(

let uu____10651 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print1 "(c) Monadic app: Binding head %s " uu____10651))
end
| uu____10652 -> begin
()
end));
(

let uu____10653 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1)
in (match (uu____10653) with
| true -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (head2)) chead1 ((FStar_Pervasives_Native.None), (comp)))
end
| uu____10656 -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
end));
)
in (

let comp2 = (FStar_TypeChecker_Util.subst_lcomp subst1 comp1)
in (

let shortcuts_evaluation_order = (

let uu____10661 = (

let uu____10662 = (FStar_Syntax_Subst.compress head2)
in uu____10662.FStar_Syntax_Syntax.n)
in (match (uu____10661) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____10666 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____10691 -> (match (uu____10691) with
| (arg, uu____10705, uu____10706) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ))))
end
| uu____10715 -> begin
(

let uu____10716 = (

let map_fun = (fun uu____10780 -> (match (uu____10780) with
| ((e, q), uu____10815, c) -> begin
(

let uu____10825 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____10825) with
| true -> begin
((FStar_Pervasives_Native.None), (((e), (q))))
end
| uu____10872 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____10875 = (

let uu____10880 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____10880), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____10875)))))
end))
end))
in (

let uu____10909 = (

let uu____10934 = (

let uu____10957 = (

let uu____10968 = (

let uu____10977 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____10977), (FStar_Pervasives_Native.None), (chead1)))
in (uu____10968)::arg_comps_rev)
in (FStar_List.map map_fun uu____10957))
in (FStar_All.pipe_left FStar_List.split uu____10934))
in (match (uu____10909) with
| (lifted_args, reverse_args) -> begin
(

let uu____11146 = (

let uu____11147 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____11147))
in (

let uu____11156 = (

let uu____11163 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____11163))
in ((lifted_args), (uu____11146), (uu____11156))))
end)))
in (match (uu____10716) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___71_11276 -> (match (uu___71_11276) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1 [] e1.FStar_Syntax_Syntax.pos)
in (

let letbinding = (

let uu____11337 = (

let uu____11344 = (

let uu____11345 = (

let uu____11358 = (

let uu____11361 = (

let uu____11362 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____11362)::[])
in (FStar_Syntax_Subst.close uu____11361 e))
in ((((false), ((lb)::[]))), (uu____11358)))
in FStar_Syntax_Syntax.Tm_let (uu____11345))
in (FStar_Syntax_Syntax.mk uu____11344))
in (uu____11337 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp2.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____11406 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp2 guard1)
in (match (uu____11406) with
| (comp3, g) -> begin
((

let uu____11423 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____11423) with
| true -> begin
(

let uu____11424 = (FStar_Syntax_Print.term_to_string app)
in (

let uu____11425 = (FStar_Syntax_Print.lcomp_to_string comp3)
in (FStar_Util.print2 "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n" uu____11424 uu____11425)))
end
| uu____11426 -> begin
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

let rec tc_args = (fun head_info uu____11501 bs args1 -> (match (uu____11501) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11634))))::rest, ((uu____11636, FStar_Pervasives_Native.None))::uu____11637) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____11697 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (match (uu____11697) with
| (t1, g_ex) -> begin
(

let uu____11710 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____11710) with
| (varg, uu____11730, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____11754 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____11754)))
in (

let uu____11755 = (

let uu____11788 = (

let uu____11799 = (

let uu____11812 = (

let uu____11813 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____11813 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____11812)))
in (uu____11799)::outargs)
in (

let uu____11832 = (

let uu____11833 = (FStar_TypeChecker_Rel.conj_guard g_ex g)
in (FStar_TypeChecker_Rel.conj_guard implicits uu____11833))
in ((subst2), (uu____11788), ((arg)::arg_rets), (uu____11832), (fvs))))
in (tc_args head_info uu____11755 rest args1))))
end))
end)))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11933)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11934))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____11947 -> begin
(

let uu____11956 = (

let uu____11961 = (

let uu____11962 = (FStar_Syntax_Print.aqual_to_string aqual)
in (

let uu____11963 = (FStar_Syntax_Print.aqual_to_string aq)
in (

let uu____11964 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____11965 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format4 "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s" uu____11962 uu____11963 uu____11964 uu____11965)))))
in ((FStar_Errors.Fatal_InconsistentImplicitQualifier), (uu____11961)))
in (FStar_Errors.raise_error uu____11956 e.FStar_Syntax_Syntax.pos))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___92_11968 = x
in {FStar_Syntax_Syntax.ppname = uu___92_11968.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___92_11968.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____11970 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____11970) with
| true -> begin
(

let uu____11971 = (FStar_Syntax_Print.bv_to_string x1)
in (

let uu____11972 = (FStar_Syntax_Print.term_to_string x1.FStar_Syntax_Syntax.sort)
in (

let uu____11973 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11974 = (FStar_Syntax_Print.subst_to_string subst1)
in (

let uu____11975 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print5 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n" uu____11971 uu____11972 uu____11973 uu____11974 uu____11975))))))
end
| uu____11976 -> begin
()
end));
(

let uu____11977 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (match (uu____11977) with
| (targ1, g_ex) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___93_11992 = env1
in {FStar_TypeChecker_Env.solver = uu___93_11992.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___93_11992.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___93_11992.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___93_11992.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___93_11992.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___93_11992.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___93_11992.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___93_11992.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___93_11992.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___93_11992.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___93_11992.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___93_11992.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___93_11992.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___93_11992.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___93_11992.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___93_11992.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___93_11992.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___93_11992.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___93_11992.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___93_11992.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___93_11992.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___93_11992.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___93_11992.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___93_11992.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___93_11992.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___93_11992.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___93_11992.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___93_11992.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___93_11992.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___93_11992.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___93_11992.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___93_11992.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___93_11992.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___93_11992.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___93_11992.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___93_11992.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___93_11992.FStar_TypeChecker_Env.dep_graph})
in ((

let uu____11994 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____11994) with
| true -> begin
(

let uu____11995 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____11996 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11997 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____11995 uu____11996 uu____11997))))
end
| uu____11998 -> begin
()
end));
(

let uu____11999 = (tc_term env2 e)
in (match (uu____11999) with
| (e1, c, g_e) -> begin
(

let g1 = (

let uu____12016 = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.conj_guard g_ex) uu____12016))
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____12035 = (

let uu____12038 = (

let uu____12045 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____12045))
in (FStar_Pervasives_Native.fst uu____12038))
in ((uu____12035), (aq)))
in (

let uu____12052 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____12052) with
| true -> begin
(

let subst2 = (

let uu____12060 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____12060 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____12121 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
)))
end));
)));
)
end
| (uu____12174, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____12210) -> begin
(

let uu____12261 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____12261) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 solve ghead2 tres -> (

let tres1 = (

let uu____12311 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____12311 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____12338 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____12338) with
| (bs2, cres'1) -> begin
(

let head_info1 = (

let uu____12360 = (FStar_Syntax_Util.lcomp_of_comp cres'1)
in ((head2), (chead1), (ghead2), (uu____12360)))
in ((

let uu____12362 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____12362) with
| true -> begin
(FStar_Errors.log_issue tres1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_RedundantExplicitCurrying), ("Potentially redundant explicit currying of a function type")))
end
| uu____12363 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____12400 when (not (norm1)) -> begin
(

let rec norm_tres = (fun tres2 -> (

let tres3 = (FStar_TypeChecker_Normalize.unfold_whnf env tres2)
in (

let uu____12408 = (

let uu____12409 = (FStar_Syntax_Subst.compress tres3)
in uu____12409.FStar_Syntax_Syntax.n)
in (match (uu____12408) with
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____12412; FStar_Syntax_Syntax.index = uu____12413; FStar_Syntax_Syntax.sort = tres4}, uu____12415) -> begin
(norm_tres tres4)
end
| uu____12422 -> begin
tres3
end))))
in (

let uu____12423 = (norm_tres tres1)
in (aux true solve ghead2 uu____12423)))
end
| uu____12424 when (not (solve)) -> begin
(

let ghead3 = (FStar_TypeChecker_Rel.solve_deferred_constraints env ghead2)
in (aux norm1 solve ghead3 tres1))
end
| uu____12426 -> begin
(

let uu____12427 = (

let uu____12432 = (

let uu____12433 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____12434 = (FStar_Util.string_of_int n_args)
in (

let uu____12441 = (FStar_Syntax_Print.term_to_string tres1)
in (FStar_Util.format3 "Too many arguments to function of type %s; got %s arguments, remaining type is %s" uu____12433 uu____12434 uu____12441))))
in ((FStar_Errors.Fatal_ToManyArgumentToFunction), (uu____12432)))
in (

let uu____12442 = (FStar_Syntax_Syntax.argpos arg)
in (FStar_Errors.raise_error uu____12427 uu____12442)))
end)))
in (aux false false ghead1 chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf guard -> (

let uu____12470 = (

let uu____12471 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____12471.FStar_Syntax_Syntax.n)
in (match (uu____12470) with
| FStar_Syntax_Syntax.Tm_uvar (uu____12480) -> begin
(

let uu____12481 = (FStar_List.fold_right (fun uu____12510 uu____12511 -> (match (uu____12511) with
| (bs, guard1) -> begin
(

let uu____12536 = (

let uu____12549 = (

let uu____12550 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12550 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____12549))
in (match (uu____12536) with
| (t, uu____12566, g) -> begin
(

let uu____12580 = (

let uu____12583 = (FStar_Syntax_Syntax.null_binder t)
in (uu____12583)::bs)
in (

let uu____12584 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in ((uu____12580), (uu____12584))))
end))
end)) args (([]), (guard)))
in (match (uu____12481) with
| (bs, guard1) -> begin
(

let uu____12601 = (

let uu____12606 = (

let uu____12619 = (

let uu____12620 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12620 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____12619))
in (match (uu____12606) with
| (t, uu____12634, g) -> begin
(

let uu____12648 = (FStar_Options.ml_ish ())
in (match (uu____12648) with
| true -> begin
(

let uu____12653 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____12654 = (FStar_TypeChecker_Rel.conj_guard guard1 g)
in ((uu____12653), (uu____12654))))
end
| uu____12655 -> begin
(

let uu____12656 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____12657 = (FStar_TypeChecker_Rel.conj_guard guard1 g)
in ((uu____12656), (uu____12657))))
end))
end))
in (match (uu____12601) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____12670 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____12670) with
| true -> begin
(

let uu____12671 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____12672 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____12673 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____12671 uu____12672 uu____12673))))
end
| uu____12674 -> begin
()
end));
(

let g = (

let uu____12676 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____12676))
in (

let uu____12677 = (FStar_TypeChecker_Rel.conj_guard g guard2)
in (check_function_app bs_cres uu____12677)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12678); FStar_Syntax_Syntax.pos = uu____12679; FStar_Syntax_Syntax.vars = uu____12680}, uu____12681) -> begin
(

let uu____12702 = (FStar_List.fold_right (fun uu____12731 uu____12732 -> (match (uu____12732) with
| (bs, guard1) -> begin
(

let uu____12757 = (

let uu____12770 = (

let uu____12771 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12771 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____12770))
in (match (uu____12757) with
| (t, uu____12787, g) -> begin
(

let uu____12801 = (

let uu____12804 = (FStar_Syntax_Syntax.null_binder t)
in (uu____12804)::bs)
in (

let uu____12805 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in ((uu____12801), (uu____12805))))
end))
end)) args (([]), (guard)))
in (match (uu____12702) with
| (bs, guard1) -> begin
(

let uu____12822 = (

let uu____12827 = (

let uu____12840 = (

let uu____12841 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12841 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____12840))
in (match (uu____12827) with
| (t, uu____12855, g) -> begin
(

let uu____12869 = (FStar_Options.ml_ish ())
in (match (uu____12869) with
| true -> begin
(

let uu____12874 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____12875 = (FStar_TypeChecker_Rel.conj_guard guard1 g)
in ((uu____12874), (uu____12875))))
end
| uu____12876 -> begin
(

let uu____12877 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____12878 = (FStar_TypeChecker_Rel.conj_guard guard1 g)
in ((uu____12877), (uu____12878))))
end))
end))
in (match (uu____12822) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____12891 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____12891) with
| true -> begin
(

let uu____12892 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____12893 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____12894 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____12892 uu____12893 uu____12894))))
end
| uu____12895 -> begin
()
end));
(

let g = (

let uu____12897 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____12897))
in (

let uu____12898 = (FStar_TypeChecker_Rel.conj_guard g guard2)
in (check_function_app bs_cres uu____12898)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____12917 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____12917) with
| (bs1, c1) -> begin
(

let head_info = (

let uu____12939 = (FStar_Syntax_Util.lcomp_of_comp c1)
in ((head1), (chead), (ghead), (uu____12939)))
in (tc_args head_info (([]), ([]), ([]), (guard), ([])) bs1 args))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____12977) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort guard)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____12983, uu____12984) -> begin
(check_function_app t guard)
end
| uu____13025 -> begin
(

let uu____13026 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in (FStar_Errors.raise_error uu____13026 head1.FStar_Syntax_Syntax.pos))
end)))
in (check_function_app thead FStar_TypeChecker_Rel.trivial_guard))));
)))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head1 chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && (Prims.op_Equality (FStar_List.length bs) (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let uu____13098 = (FStar_List.fold_left2 (fun uu____13145 uu____13146 uu____13147 -> (match (((uu____13145), (uu____13146), (uu____13147))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((Prims.op_disEquality aq aq')) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InconsistentImplicitQualifier), ("Inconsistent implicit qualifiers")) e.FStar_Syntax_Syntax.pos)
end
| uu____13226 -> begin
()
end);
(

let uu____13227 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____13227) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____13247 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____13247 g))
in (

let ghost1 = (ghost || ((

let uu____13251 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____13251))) && (

let uu____13253 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____13253)))))
in (

let uu____13254 = (

let uu____13257 = (

let uu____13260 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____13260)::[])
in (FStar_List.append seen uu____13257))
in (

let uu____13261 = (FStar_TypeChecker_Rel.conj_guard guard g1)
in ((uu____13254), (uu____13261), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____13098) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____13283 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____13283 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____13284 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____13285 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____13285) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____13301 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp) * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____13344 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____13344) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____13389 = branch1
in (match (uu____13389) with
| (cpat, uu____13430, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let tc_annot = (fun env1 t -> (

let uu____13507 = (FStar_Syntax_Util.type_u ())
in (match (uu____13507) with
| (tu, u) -> begin
(

let uu____13518 = (tc_check_tot_or_gtot_term env1 t tu)
in (match (uu____13518) with
| (t1, uu____13530, g) -> begin
((t1), (g))
end))
end)))
in (

let uu____13532 = (FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 tc_annot)
in (match (uu____13532) with
| (pat_bvs1, exp, guard_pat_annots, p) -> begin
((

let uu____13566 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13566) with
| true -> begin
(

let uu____13567 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____13568 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____13567 uu____13568)))
end
| uu____13569 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs1)
in (

let uu____13571 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____13571) with
| (env1, uu____13593) -> begin
(

let env11 = (

let uu___94_13599 = env1
in {FStar_TypeChecker_Env.solver = uu___94_13599.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___94_13599.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___94_13599.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___94_13599.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___94_13599.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___94_13599.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___94_13599.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___94_13599.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___94_13599.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___94_13599.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___94_13599.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___94_13599.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___94_13599.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___94_13599.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___94_13599.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___94_13599.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___94_13599.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___94_13599.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___94_13599.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___94_13599.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___94_13599.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___94_13599.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___94_13599.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___94_13599.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___94_13599.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___94_13599.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___94_13599.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___94_13599.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___94_13599.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___94_13599.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___94_13599.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___94_13599.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___94_13599.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___94_13599.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___94_13599.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___94_13599.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___94_13599.FStar_TypeChecker_Env.dep_graph})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in ((

let uu____13602 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13602) with
| true -> begin
(

let uu____13603 = (FStar_Syntax_Print.term_to_string exp)
in (

let uu____13604 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____13603 uu____13604)))
end
| uu____13605 -> begin
()
end));
(

let env12 = (FStar_TypeChecker_Env.set_expected_typ env11 expected_pat_t)
in (

let uu____13607 = (tc_tot_or_gtot_term env12 exp)
in (match (uu____13607) with
| (exp1, lc, g) -> begin
(

let g1 = (

let uu___95_13632 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___95_13632.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___95_13632.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___95_13632.FStar_TypeChecker_Env.implicits})
in (

let uu____13633 = (

let uu____13634 = (FStar_TypeChecker_Rel.teq_nosmt env12 lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (match (uu____13634) with
| true -> begin
(

let env13 = (FStar_TypeChecker_Env.set_range env12 exp1.FStar_Syntax_Syntax.pos)
in (

let uu____13636 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env13 g1)
in (FStar_All.pipe_right uu____13636 (FStar_TypeChecker_Rel.resolve_implicits env13))))
end
| uu____13637 -> begin
(

let uu____13638 = (

let uu____13643 = (

let uu____13644 = (FStar_Syntax_Print.term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____13645 = (FStar_Syntax_Print.term_to_string expected_pat_t)
in (FStar_Util.format2 "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)" uu____13644 uu____13645)))
in ((FStar_Errors.Fatal_MismatchedPatternType), (uu____13643)))
in (FStar_Errors.raise_error uu____13638 exp1.FStar_Syntax_Syntax.pos))
end))
in (

let norm_exp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env12 exp1)
in (

let uvs_to_string = (fun uvs -> (

let uu____13657 = (

let uu____13660 = (FStar_Util.set_elements uvs)
in (FStar_All.pipe_right uu____13660 (FStar_List.map (fun u -> (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)))))
in (FStar_All.pipe_right uu____13657 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars norm_exp)
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____13678 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Free")))
in (match (uu____13678) with
| true -> begin
((

let uu____13680 = (FStar_Syntax_Print.term_to_string norm_exp)
in (

let uu____13681 = (uvs_to_string uvs1)
in (FStar_Util.print2 ">> free_1(%s) = %s\n" uu____13680 uu____13681)));
(

let uu____13682 = (FStar_Syntax_Print.term_to_string expected_pat_t)
in (

let uu____13683 = (uvs_to_string uvs2)
in (FStar_Util.print2 ">> free_2(%s) = %s\n" uu____13682 uu____13683)));
)
end
| uu____13684 -> begin
()
end));
(

let uu____13686 = (

let uu____13687 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____13687))
in (match (uu____13686) with
| true -> begin
(

let unresolved = (FStar_Util.set_difference uvs1 uvs2)
in (

let uu____13691 = (

let uu____13696 = (

let uu____13697 = (FStar_TypeChecker_Normalize.term_to_string env norm_exp)
in (

let uu____13698 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____13699 = (uvs_to_string unresolved)
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____13697 uu____13698 uu____13699))))
in ((FStar_Errors.Fatal_UnresolvedPatternVar), (uu____13696)))
in (FStar_Errors.raise_error uu____13691 p.FStar_Syntax_Syntax.p)))
end
| uu____13700 -> begin
()
end));
(

let uu____13702 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13702) with
| true -> begin
(

let uu____13703 = (FStar_TypeChecker_Normalize.term_to_string env exp1)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____13703))
end
| uu____13704 -> begin
()
end));
(

let p1 = (FStar_TypeChecker_Util.decorate_pattern env p exp1)
in ((p1), (pat_bvs1), (pat_env), (exp1), (guard_pat_annots), (norm_exp)));
)))))))
end)));
)))
end)));
)
end))))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let uu____13712 = (

let uu____13719 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____13719 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____13712) with
| (scrutinee_env, uu____13752) -> begin
(

let uu____13757 = (tc_pat true pat_t pattern)
in (match (uu____13757) with
| (pattern1, pat_bvs1, pat_env, pat_exp, guard_pat_annots, norm_pat_exp) -> begin
(

let uu____13807 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____13837 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____13837) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_WhenClauseNotSupported), ("When clauses are not yet supported in --verify mode; they will be some day")) e.FStar_Syntax_Syntax.pos)
end
| uu____13854 -> begin
(

let uu____13855 = (

let uu____13862 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_Syntax_Util.t_bool)
in (tc_term uu____13862 e))
in (match (uu____13855) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____13807) with
| (when_clause1, g_when) -> begin
(

let uu____13911 = (tc_term pat_env branch_exp)
in (match (uu____13911) with
| (branch_exp1, c, g_branch) -> begin
(

let g_branch1 = (FStar_TypeChecker_Rel.conj_guard guard_pat_annots g_branch)
in (

let when_condition = (match (when_clause1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____13959 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) uu____13959))
end)
in (

let uu____13962 = (

let eqs = (

let uu____13983 = (

let uu____13984 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____13984)))
in (match (uu____13983) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13991 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____13997) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____14000) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____14003) -> begin
FStar_Pervasives_Native.None
end
| uu____14006 -> begin
(

let uu____14007 = (

let uu____14008 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____14008 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____14007))
end))
end))
in (

let uu____14009 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch1)
in (match (uu____14009) with
| (c1, g_branch2) -> begin
(

let uu____14034 = (match (((eqs), (when_condition))) with
| uu____14049 when (

let uu____14060 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____14060))) -> begin
((c1), (g_when))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
((c1), (g_when))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (

let uu____14082 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____14083 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____14082), (uu____14083))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____14098 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____14098))
in (

let uu____14099 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____14100 = (

let uu____14101 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____14101 g_when))
in ((uu____14099), (uu____14100))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____14113 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____14113), (g_when)))))
end)
in (match (uu____14034) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let maybe_return_c_weak = (fun should_return -> (

let c_weak1 = (

let uu____14149 = (should_return && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c_weak))
in (match (uu____14149) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env branch_exp1 c_weak)
end
| uu____14150 -> begin
c_weak
end))
in (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak1)))
in (

let uu____14151 = (FStar_TypeChecker_Rel.close_guard env binders g_when_weak)
in ((c_weak.FStar_Syntax_Syntax.eff_name), (c_weak.FStar_Syntax_Syntax.cflags), (maybe_return_c_weak), (uu____14151), (g_branch2)))))
end))
end)))
in (match (uu____13962) with
| (effect_label, cflags, maybe_return_c, g_when1, g_branch2) -> begin
(

let branch_guard = (

let uu____14200 = (

let uu____14201 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____14201)))
in (match (uu____14200) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____14204 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____14245 = (

let uu____14246 = (

let uu____14247 = (

let uu____14250 = (

let uu____14257 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____14257))
in (FStar_Pervasives_Native.snd uu____14250))
in (FStar_List.length uu____14247))
in (uu____14246 > (Prims.parse_int "1")))
in (match (uu____14245) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____14263 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____14263) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____14284 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____14299 = (

let uu____14304 = (

let uu____14305 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____14305)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____14304))
in (uu____14299 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____14326 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____14326)::[])))
end)))
end
| uu____14327 -> begin
[]
end)))
in (

let fail1 = (fun uu____14333 -> (

let uu____14334 = (

let uu____14335 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____14336 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____14337 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____14335 uu____14336 uu____14337))))
in (failwith uu____14334)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____14350) -> begin
(head_constructor t1)
end
| uu____14355 -> begin
(fail1 ())
end))
in (

let pat_exp2 = (

let uu____14359 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____14359 FStar_Syntax_Util.unmeta))
in (match (pat_exp2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____14364) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____14365); FStar_Syntax_Syntax.pos = uu____14366; FStar_Syntax_Syntax.vars = uu____14367}, uu____14368) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_name (uu____14389) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (c1) -> begin
(

let uu____14391 = (

let uu____14392 = (tc_constant env pat_exp2.FStar_Syntax_Syntax.pos c1)
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____14392 scrutinee_tm1 pat_exp2))
in (uu____14391)::[])
end
| FStar_Syntax_Syntax.Tm_uinst (uu____14393) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____14401 = (

let uu____14402 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____14402)))
in (match (uu____14401) with
| true -> begin
[]
end
| uu____14405 -> begin
(

let uu____14406 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____14406))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____14409) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____14411 = (

let uu____14412 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____14412)))
in (match (uu____14411) with
| true -> begin
[]
end
| uu____14415 -> begin
(

let uu____14416 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____14416))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let f = (head_constructor head1)
in (

let uu____14442 = (

let uu____14443 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____14443)))
in (match (uu____14442) with
| true -> begin
[]
end
| uu____14446 -> begin
(

let sub_term_guards = (

let uu____14450 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____14482 -> (match (uu____14482) with
| (ei, uu____14492) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____14498 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____14498) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____14519 -> begin
(

let sub_term = (

let uu____14533 = (

let uu____14538 = (

let uu____14539 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar uu____14539 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None))
in (

let uu____14540 = (

let uu____14541 = (FStar_Syntax_Syntax.as_arg scrutinee_tm1)
in (uu____14541)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____14538 uu____14540)))
in (uu____14533 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____14450 FStar_List.flatten))
in (

let uu____14568 = (discriminate scrutinee_tm1 f)
in (FStar_List.append uu____14568 sub_term_guards)))
end)))
end
| uu____14571 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pat -> (

let uu____14587 = (

let uu____14588 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____14588)))
in (match (uu____14587) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____14589 -> begin
(

let t = (

let uu____14591 = (build_branch_guard scrutinee_tm1 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____14591))
in (

let uu____14600 = (FStar_Syntax_Util.type_u ())
in (match (uu____14600) with
| (k, uu____14606) -> begin
(

let uu____14607 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____14607) with
| (t1, uu____14615, uu____14616) -> begin
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

let guard = (FStar_TypeChecker_Rel.conj_guard g_when1 g_branch2)
in ((

let uu____14626 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____14626) with
| true -> begin
(

let uu____14627 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____14627))
end
| uu____14628 -> begin
()
end));
(

let uu____14629 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in (

let uu____14646 = (

let uu____14647 = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (FStar_TypeChecker_Util.close_guard_implicits env uu____14647 guard))
in ((uu____14629), (branch_guard), (effect_label), (cflags), (maybe_return_c), (uu____14646))));
)))
end))))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let uu____14688 = (check_let_bound_def true env1 lb)
in (match (uu____14688) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____14710 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____14727 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____14727), (univ_vars1), (c1)))
end
| uu____14728 -> begin
(

let g11 = (

let uu____14730 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____14730 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let uu____14732 = (

let uu____14745 = (

let uu____14760 = (

let uu____14769 = (

let uu____14776 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____14776)))
in (uu____14769)::[])
in (FStar_TypeChecker_Util.generalize env1 false uu____14760))
in (FStar_List.hd uu____14745))
in (match (uu____14732) with
| (uu____14809, univs1, e11, c11, gvs) -> begin
(

let g12 = (FStar_All.pipe_left (FStar_TypeChecker_Rel.map_guard g11) (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env1))
in (

let g13 = (FStar_TypeChecker_Rel.abstract_guard_n gvs g12)
in (

let uu____14823 = (FStar_Syntax_Util.lcomp_of_comp c11)
in ((g13), (e11), (univs1), (uu____14823)))))
end)))
end)
in (match (uu____14710) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____14834 = (

let uu____14841 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____14841) with
| true -> begin
(

let uu____14848 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____14848) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____14869 -> begin
((

let uu____14871 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____14871 FStar_TypeChecker_Err.top_level_effect));
(

let uu____14872 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____14872), (c12)));
)
end)
end))
end
| uu____14879 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____14884 = (FStar_Syntax_Syntax.lcomp_comp c11)
in (FStar_All.pipe_right uu____14884 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env1)))
in (

let e21 = (

let uu____14890 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____14890) with
| true -> begin
e2
end
| uu____14893 -> begin
((

let uu____14895 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____14895 FStar_TypeChecker_Err.top_level_effect));
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos);
)
end))
in ((e21), (c))));
)
end))
in (match (uu____14834) with
| (e21, c12) -> begin
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit)
in (

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e11 lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
in (

let uu____14918 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____14929 = (FStar_Syntax_Util.lcomp_of_comp cres)
in ((uu____14918), (uu____14929), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| uu____14930 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___96_14961 = env1
in {FStar_TypeChecker_Env.solver = uu___96_14961.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_14961.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_14961.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_14961.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___96_14961.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___96_14961.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_14961.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_14961.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_14961.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_14961.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_14961.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_14961.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_14961.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___96_14961.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___96_14961.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___96_14961.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___96_14961.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_14961.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___96_14961.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___96_14961.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___96_14961.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___96_14961.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___96_14961.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___96_14961.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_14961.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___96_14961.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_14961.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___96_14961.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___96_14961.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___96_14961.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___96_14961.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___96_14961.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___96_14961.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___96_14961.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___96_14961.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___96_14961.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___96_14961.FStar_TypeChecker_Env.dep_graph})
in (

let uu____14962 = (

let uu____14973 = (

let uu____14974 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____14974 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____14973 lb))
in (match (uu____14962) with
| (e1, uu____14996, c1, g1, annotated) -> begin
((

let uu____15001 = ((FStar_Util.for_some (FStar_Syntax_Util.is_fvar FStar_Parser_Const.inline_let_attr) lb.FStar_Syntax_Syntax.lbattrs) && (

let uu____15005 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c1)
in (not (uu____15005))))
in (match (uu____15001) with
| true -> begin
(

let uu____15006 = (

let uu____15011 = (

let uu____15012 = (FStar_Syntax_Print.term_to_string e1)
in (

let uu____15013 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.format2 "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\"" uu____15012 uu____15013)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____15011)))
in (FStar_Errors.raise_error uu____15006 e1.FStar_Syntax_Syntax.pos))
end
| uu____15014 -> begin
()
end));
(

let x = (

let uu___97_15016 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___97_15016.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___97_15016.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____15017 = (

let uu____15022 = (

let uu____15023 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____15023)::[])
in (FStar_Syntax_Subst.open_term uu____15022 e2))
in (match (uu____15017) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let env_x = (FStar_TypeChecker_Env.push_bv env2 x1)
in (

let uu____15055 = (tc_term env_x e21)
in (match (uu____15055) with
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

let uu____15080 = (

let uu____15087 = (

let uu____15088 = (

let uu____15101 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____15101)))
in FStar_Syntax_Syntax.Tm_let (uu____15088))
in (FStar_Syntax_Syntax.mk uu____15087))
in (uu____15080 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____15119 = (

let uu____15120 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____15121 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____15120 c1.FStar_Syntax_Syntax.res_typ uu____15121 e11)))
in (FStar_All.pipe_left (fun _0_19 -> FStar_TypeChecker_Common.NonTrivial (_0_19)) uu____15119))
in (

let g21 = (

let uu____15123 = (

let uu____15124 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____15124 g2))
in (FStar_TypeChecker_Rel.close_guard env2 xb uu____15123))
in (

let g22 = (FStar_TypeChecker_Util.close_guard_implicits env2 xb g21)
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g22)
in (

let uu____15127 = (

let uu____15128 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____15128))
in (match (uu____15127) with
| true -> begin
(

let tt = (

let uu____15138 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____15138 FStar_Option.get))
in ((

let uu____15144 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____15144) with
| true -> begin
(

let uu____15145 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____15146 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____15145 uu____15146)))
end
| uu____15147 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____15148 -> begin
(

let uu____15149 = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____15149) with
| (t, g_ex) -> begin
((

let uu____15163 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____15163) with
| true -> begin
(

let uu____15164 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____15165 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____15164 uu____15165)))
end
| uu____15166 -> begin
()
end));
(

let uu____15167 = (FStar_TypeChecker_Rel.conj_guard g_ex guard)
in ((e4), ((

let uu___98_15169 = cres
in {FStar_Syntax_Syntax.eff_name = uu___98_15169.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___98_15169.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___98_15169.FStar_Syntax_Syntax.comp_thunk})), (uu____15167)));
)
end))
end))))))))))))
end)))))
end)));
)
end)))
end
| uu____15170 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____15202 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____15202) with
| (lbs1, e21) -> begin
(

let uu____15221 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____15221) with
| (env0, topt) -> begin
(

let uu____15240 = (build_let_rec_env true env0 lbs1)
in (match (uu____15240) with
| (lbs2, rec_env) -> begin
(

let uu____15259 = (check_let_recs rec_env lbs2)
in (match (uu____15259) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____15279 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g_lbs)
in (FStar_All.pipe_right uu____15279 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let all_lb_names = (

let uu____15285 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____15285 (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((Prims.op_Equality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
lb
end
| uu____15317 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)))))
end
| uu____15318 -> begin
(

let ecs = (

let uu____15334 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____15368 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____15368))))))
in (FStar_TypeChecker_Util.generalize env1 true uu____15334))
in (FStar_List.map2 (fun uu____15402 lb -> (match (uu____15402) with
| (x, uvs, e, c, gvs) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)) ecs lbs3))
end)
in (

let cres = (

let uu____15450 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____15450))
in (

let uu____15451 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____15451) with
| (lbs5, e22) -> begin
((

let uu____15471 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____15471 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____15472 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____15472), (cres), (FStar_TypeChecker_Rel.trivial_guard)));
)
end))))))
end))
end))
end))
end))
end
| uu____15483 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____15515 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____15515) with
| (lbs1, e21) -> begin
(

let uu____15534 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____15534) with
| (env0, topt) -> begin
(

let uu____15553 = (build_let_rec_env false env0 lbs1)
in (match (uu____15553) with
| (lbs2, rec_env) -> begin
(

let uu____15572 = (check_let_recs rec_env lbs2)
in (match (uu____15572) with
| (lbs3, g_lbs) -> begin
(

let uu____15591 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___99_15614 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___99_15614.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___99_15614.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___100_15616 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___100_15616.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___100_15616.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___100_15616.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___100_15616.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___100_15616.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___100_15616.FStar_Syntax_Syntax.lbpos})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____15591) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____15643 = (tc_term env2 e21)
in (match (uu____15643) with
| (e22, cres, g2) -> begin
(

let cres1 = (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e22 cres)
in (

let cres2 = (FStar_Syntax_Util.lcomp_set_flags cres1 ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
in (

let guard = (

let uu____15662 = (

let uu____15663 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Rel.close_guard env2 uu____15663 g2))
in (FStar_TypeChecker_Rel.conj_guard g_lbs uu____15662))
in (

let cres3 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres2)
in (

let tres = (norm env2 cres3.FStar_Syntax_Syntax.res_typ)
in (

let cres4 = (

let uu___101_15671 = cres3
in {FStar_Syntax_Syntax.eff_name = uu___101_15671.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___101_15671.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___101_15671.FStar_Syntax_Syntax.comp_thunk})
in (

let guard1 = (

let bs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (

let uu____15679 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____15679)))))
in (FStar_TypeChecker_Util.close_guard_implicits env2 bs guard))
in (

let uu____15680 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____15680) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____15718) -> begin
((e), (cres4), (guard1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____15719 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (match (uu____15719) with
| (tres1, g_ex) -> begin
(

let cres5 = (

let uu___102_15733 = cres4
in {FStar_Syntax_Syntax.eff_name = uu___102_15733.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___102_15733.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___102_15733.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____15734 = (FStar_TypeChecker_Rel.conj_guard g_ex guard1)
in ((e), (cres5), (uu____15734))))
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
| uu____15735 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let uu____15778 = (FStar_Options.ml_ish ())
in (match (uu____15778) with
| true -> begin
false
end
| uu____15779 -> begin
(

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____15781 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____15781) with
| (formals, c) -> begin
(

let uu____15806 = (FStar_Syntax_Util.abs_formals lbdef)
in (match (uu____15806) with
| (actuals, uu____15816, uu____15817) -> begin
(match ((((FStar_List.length formals) < (Prims.parse_int "1")) || ((FStar_List.length actuals) < (Prims.parse_int "1")))) with
| true -> begin
(

let uu____15830 = (

let uu____15835 = (

let uu____15836 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____15837 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____15836 uu____15837)))
in ((FStar_Errors.Fatal_RecursiveFunctionLiteral), (uu____15835)))
in (FStar_Errors.raise_error uu____15830 lbtyp.FStar_Syntax_Syntax.pos))
end
| uu____15838 -> begin
(

let actuals1 = (

let uu____15840 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____15840 actuals))
in ((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____15861 -> begin
(

let uu____15862 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____15862))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____15880 -> begin
(

let uu____15881 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____15881))
end))
in (

let msg = (

let uu____15889 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____15890 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____15889 uu____15890 formals_msg actuals_msg)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_LetRecArgumentMismatch), (msg)) lbdef.FStar_Syntax_Syntax.pos))))
end
| uu____15891 -> begin
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

let uu____15897 = (FStar_List.fold_left (fun uu____15923 lb -> (match (uu____15923) with
| (lbs1, env1) -> begin
(

let uu____15943 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____15943) with
| (univ_vars1, t, check_t) -> begin
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univ_vars1)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t1 = (match ((not (check_t))) with
| true -> begin
t
end
| uu____15962 -> begin
(

let env01 = (FStar_TypeChecker_Env.push_univ_vars env0 univ_vars1)
in (

let uu____15964 = (

let uu____15971 = (

let uu____15972 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15972))
in (tc_check_tot_or_gtot_term (

let uu___103_15983 = env01
in {FStar_TypeChecker_Env.solver = uu___103_15983.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___103_15983.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___103_15983.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___103_15983.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___103_15983.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___103_15983.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___103_15983.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___103_15983.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___103_15983.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___103_15983.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___103_15983.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___103_15983.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___103_15983.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___103_15983.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___103_15983.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___103_15983.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___103_15983.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___103_15983.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___103_15983.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___103_15983.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___103_15983.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___103_15983.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___103_15983.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___103_15983.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___103_15983.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___103_15983.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___103_15983.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___103_15983.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___103_15983.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___103_15983.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___103_15983.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___103_15983.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___103_15983.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___103_15983.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___103_15983.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___103_15983.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___103_15983.FStar_TypeChecker_Env.dep_graph}) t uu____15971))
in (match (uu____15964) with
| (t1, uu____15985, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.resolve_implicits env2 g)
in ((

let uu____15989 = (FStar_TypeChecker_Rel.discharge_guard env2 g1)
in (FStar_All.pipe_left (fun a238 -> ()) uu____15989));
(norm env01 t1);
))
end)))
end)
in (

let env3 = (

let uu____15991 = (termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1)
in (match (uu____15991) with
| true -> begin
(

let uu___104_15992 = env2
in {FStar_TypeChecker_Env.solver = uu___104_15992.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___104_15992.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___104_15992.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___104_15992.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___104_15992.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___104_15992.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___104_15992.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___104_15992.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___104_15992.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___104_15992.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___104_15992.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___104_15992.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___104_15992.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1), (univ_vars1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___104_15992.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___104_15992.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___104_15992.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___104_15992.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___104_15992.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___104_15992.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___104_15992.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___104_15992.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___104_15992.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___104_15992.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___104_15992.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___104_15992.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___104_15992.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___104_15992.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___104_15992.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___104_15992.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___104_15992.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___104_15992.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___104_15992.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___104_15992.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___104_15992.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___104_15992.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___104_15992.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___104_15992.FStar_TypeChecker_Env.dep_graph})
end
| uu____15999 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname ((univ_vars1), (t1)))
end))
in (

let lb1 = (

let uu___105_16005 = lb
in {FStar_Syntax_Syntax.lbname = uu___105_16005.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___105_16005.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___105_16005.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___105_16005.FStar_Syntax_Syntax.lbpos})
in (((lb1)::lbs1), (env3)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____15897) with
| (lbs1, env1) -> begin
(((FStar_List.rev lbs1)), (env1))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____16028 = (

let uu____16037 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____16063 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____16063) with
| (bs, t, lcomp) -> begin
(match (bs) with
| [] -> begin
(

let uu____16091 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_RecursiveFunctionLiteral), ("Only function literals may be defined recursively")) uu____16091))
end
| uu____16096 -> begin
(

let lb1 = (

let uu___106_16099 = lb
in (

let uu____16100 = (FStar_Syntax_Util.abs bs t lcomp)
in {FStar_Syntax_Syntax.lbname = uu___106_16099.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___106_16099.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___106_16099.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___106_16099.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____16100; FStar_Syntax_Syntax.lbattrs = uu___106_16099.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___106_16099.FStar_Syntax_Syntax.lbpos}))
in (

let uu____16103 = (

let uu____16110 = (FStar_TypeChecker_Env.set_expected_typ env lb1.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____16110 lb1.FStar_Syntax_Syntax.lbdef))
in (match (uu____16103) with
| (e, c, g) -> begin
((

let uu____16119 = (

let uu____16120 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____16120)))
in (match (uu____16119) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedGTotForLetRec), ("Expected let rec to be a Tot term; got effect GTot")) e.FStar_Syntax_Syntax.pos)
end
| uu____16121 -> begin
()
end));
(

let lb2 = (FStar_Syntax_Util.mk_letbinding lb1.FStar_Syntax_Syntax.lbname lb1.FStar_Syntax_Syntax.lbunivs lb1.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e lb1.FStar_Syntax_Syntax.lbattrs lb1.FStar_Syntax_Syntax.lbpos)
in ((lb2), (g)));
)
end)))
end)
end)))))
in (FStar_All.pipe_right uu____16037 FStar_List.unzip))
in (match (uu____16028) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____16169 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____16169) with
| (env1, uu____16187) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____16195 = (check_lbtyp top_level env lb)
in (match (uu____16195) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (Prims.op_disEquality univ_vars1 []))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UniversePolymorphicInnerLetBound), ("Inner let-bound definitions cannot be universe polymorphic")) e1.FStar_Syntax_Syntax.pos)
end
| uu____16236 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____16239 = (tc_maybe_toplevel_term (

let uu___107_16248 = env11
in {FStar_TypeChecker_Env.solver = uu___107_16248.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___107_16248.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___107_16248.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___107_16248.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___107_16248.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___107_16248.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___107_16248.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___107_16248.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___107_16248.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___107_16248.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___107_16248.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___107_16248.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___107_16248.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___107_16248.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___107_16248.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___107_16248.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___107_16248.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___107_16248.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___107_16248.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___107_16248.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___107_16248.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___107_16248.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___107_16248.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___107_16248.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___107_16248.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___107_16248.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___107_16248.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___107_16248.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___107_16248.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___107_16248.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___107_16248.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___107_16248.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___107_16248.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___107_16248.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___107_16248.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___107_16248.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___107_16248.FStar_TypeChecker_Env.dep_graph}) e11)
in (match (uu____16239) with
| (e12, c1, g1) -> begin
(

let uu____16262 = (

let uu____16267 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____16272 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____16267 e12 c1 wf_annot))
in (match (uu____16262) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____16287 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____16287) with
| true -> begin
(

let uu____16288 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____16289 = (FStar_Syntax_Print.lcomp_to_string c11)
in (

let uu____16290 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked let-bound def %s : %s guard is %s\n" uu____16288 uu____16289 uu____16290))))
end
| uu____16291 -> begin
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

let uu____16324 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____16324) with
| (univ_opening, univ_vars1) -> begin
(

let uu____16357 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in ((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____16357)))
end))
end
| uu____16362 -> begin
(

let uu____16363 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____16363) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____16412 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____16412)))
end
| uu____16417 -> begin
(

let uu____16418 = (FStar_Syntax_Util.type_u ())
in (match (uu____16418) with
| (k, uu____16438) -> begin
(

let uu____16439 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____16439) with
| (t2, uu____16461, g) -> begin
((

let uu____16464 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____16464) with
| true -> begin
(

let uu____16465 = (

let uu____16466 = (FStar_Syntax_Util.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____16466))
in (

let uu____16467 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____16465 uu____16467)))
end
| uu____16468 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____16470 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____16470))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____16476 -> (match (uu____16476) with
| (x, imp) -> begin
(

let uu____16495 = (FStar_Syntax_Util.type_u ())
in (match (uu____16495) with
| (tu, u) -> begin
((

let uu____16515 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____16515) with
| true -> begin
(

let uu____16516 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____16517 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____16518 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____16516 uu____16517 uu____16518))))
end
| uu____16519 -> begin
()
end));
(

let uu____16520 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____16520) with
| (t, uu____16540, g) -> begin
(

let x1 = (((

let uu___108_16548 = x
in {FStar_Syntax_Syntax.ppname = uu___108_16548.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___108_16548.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____16550 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____16550) with
| true -> begin
(

let uu____16551 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____16552 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____16551 uu____16552)))
end
| uu____16553 -> begin
()
end));
(

let uu____16554 = (push_binding env x1)
in ((x1), (uu____16554), (g), (u)));
))
end));
)
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes) = (fun env bs -> (

let rec aux = (fun env1 bs1 -> (match (bs1) with
| [] -> begin
(([]), (env1), (FStar_TypeChecker_Rel.trivial_guard), ([]))
end
| (b)::bs2 -> begin
(

let uu____16648 = (tc_binder env1 b)
in (match (uu____16648) with
| (b1, env', g, u) -> begin
(

let uu____16689 = (aux env' bs2)
in (match (uu____16689) with
| (bs3, env'1, g', us) -> begin
(

let uu____16742 = (

let uu____16743 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____16743))
in (((b1)::bs3), (env'1), (uu____16742), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____16832 uu____16833 -> (match (((uu____16832), (uu____16833))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____16902 = (tc_term env1 t)
in (match (uu____16902) with
| (t1, uu____16920, g') -> begin
(

let uu____16922 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____16922)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____16964 -> (match (uu____16964) with
| (pats1, g) -> begin
(

let uu____16989 = (tc_args env p)
in (match (uu____16989) with
| (args, g') -> begin
(

let uu____17002 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats1), (uu____17002)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____17015 = (tc_maybe_toplevel_term env e)
in (match (uu____17015) with
| (e1, c, g) -> begin
(

let uu____17031 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____17031) with
| true -> begin
((e1), (c), (g))
end
| uu____17038 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (FStar_Syntax_Syntax.lcomp_comp c)
in (

let c2 = (norm_c env c1)
in (

let uu____17042 = (

let uu____17047 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____17047) with
| true -> begin
(

let uu____17052 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____17052), (false)))
end
| uu____17053 -> begin
(

let uu____17054 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____17054), (true)))
end))
in (match (uu____17042) with
| (target_comp, allow_ghost) -> begin
(

let uu____17063 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____17063) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____17073 = (FStar_Syntax_Util.lcomp_of_comp target_comp)
in (

let uu____17074 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in ((e1), (uu____17073), (uu____17074))))
end
| uu____17075 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____17084 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in (FStar_Errors.raise_error uu____17084 e1.FStar_Syntax_Syntax.pos))
end
| uu____17095 -> begin
(

let uu____17096 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in (FStar_Errors.raise_error uu____17096 e1.FStar_Syntax_Syntax.pos))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____17119 = (tc_tot_or_gtot_term env t)
in (match (uu____17119) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____17151 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____17151) with
| true -> begin
(

let uu____17152 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____17152))
end
| uu____17153 -> begin
()
end));
(

let env1 = (

let uu___109_17155 = env
in {FStar_TypeChecker_Env.solver = uu___109_17155.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___109_17155.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___109_17155.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___109_17155.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___109_17155.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___109_17155.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___109_17155.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___109_17155.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___109_17155.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___109_17155.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___109_17155.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___109_17155.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___109_17155.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___109_17155.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___109_17155.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___109_17155.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___109_17155.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___109_17155.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___109_17155.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___109_17155.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___109_17155.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___109_17155.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___109_17155.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___109_17155.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___109_17155.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___109_17155.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___109_17155.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___109_17155.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___109_17155.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___109_17155.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___109_17155.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___109_17155.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___109_17155.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___109_17155.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___109_17155.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___109_17155.FStar_TypeChecker_Env.dep_graph})
in (

let uu____17162 = (FStar_All.try_with (fun uu___111_17176 -> (match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)) (fun uu___110_17188 -> (match (uu___110_17188) with
| FStar_Errors.Error (e1, msg, uu____17197) -> begin
(

let uu____17198 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((e1), (msg)) uu____17198))
end)))
in (match (uu____17162) with
| (t, c, g) -> begin
(

let uu____17214 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____17214) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____17221 -> begin
(

let uu____17222 = (

let uu____17227 = (

let uu____17228 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____17228))
in ((FStar_Errors.Fatal_UnexpectedImplictArgument), (uu____17227)))
in (

let uu____17229 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____17222 uu____17229)))
end))
end)));
))


let level_of_type_fail : 'Auu____17244 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  'Auu____17244 = (fun env e t -> (

let uu____17260 = (

let uu____17265 = (

let uu____17266 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____17266 t))
in ((FStar_Errors.Fatal_UnexpectedTermType), (uu____17265)))
in (

let uu____17267 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____17260 uu____17267))))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____17302 = (

let uu____17303 = (FStar_Syntax_Util.unrefine t1)
in uu____17303.FStar_Syntax_Syntax.n)
in (match (uu____17302) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____17307 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____17309 -> begin
(

let uu____17310 = (FStar_Syntax_Util.type_u ())
in (match (uu____17310) with
| (t_u, u) -> begin
(

let env1 = (

let uu___112_17318 = env
in {FStar_TypeChecker_Env.solver = uu___112_17318.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___112_17318.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___112_17318.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___112_17318.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___112_17318.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___112_17318.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___112_17318.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___112_17318.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___112_17318.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___112_17318.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___112_17318.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___112_17318.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___112_17318.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___112_17318.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___112_17318.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___112_17318.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___112_17318.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___112_17318.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___112_17318.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___112_17318.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___112_17318.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___112_17318.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___112_17318.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___112_17318.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___112_17318.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___112_17318.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___112_17318.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___112_17318.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___112_17318.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___112_17318.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___112_17318.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___112_17318.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___112_17318.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___112_17318.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___112_17318.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___112_17318.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___112_17318.FStar_TypeChecker_Env.dep_graph})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____17322 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____17322))
end
| uu____17323 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____17340 = (

let uu____17341 = (FStar_Syntax_Subst.compress e)
in uu____17341.FStar_Syntax_Syntax.n)
in (match (uu____17340) with
| FStar_Syntax_Syntax.Tm_bvar (uu____17346) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____17351) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____17378) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____17394) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
u.FStar_Syntax_Syntax.ctx_uvar_typ
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____17419) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____17426 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17426) with
| ((uu____17437, t), uu____17439) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____17445 = (FStar_Syntax_Util.unfold_lazy i)
in (universe_of_aux env uu____17445))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____17448, (FStar_Util.Inl (t), uu____17450), uu____17451) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____17498, (FStar_Util.Inr (c), uu____17500), uu____17501) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____17549) -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant env e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____17558; FStar_Syntax_Syntax.vars = uu____17559}, us) -> begin
(

let uu____17565 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17565) with
| ((us', t), uu____17578) -> begin
((match ((Prims.op_disEquality (FStar_List.length us) (FStar_List.length us'))) with
| true -> begin
(

let uu____17584 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), ("Unexpected number of universe instantiations")) uu____17584))
end
| uu____17585 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____17600 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____17601) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____17611) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____17634 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____17634) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____17654 -> (match (uu____17654) with
| (b, uu____17660) -> begin
(

let uu____17661 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____17661))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____17668 = (universe_of_aux env res)
in (level_of_type env res uu____17668)))
in (

let u_c = (

let uu____17672 = (FStar_TypeChecker_Env.effect_repr env c1 u_res)
in (match (uu____17672) with
| FStar_Pervasives_Native.None -> begin
u_res
end
| FStar_Pervasives_Native.Some (trepr) -> begin
(

let uu____17676 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____17676))
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
| FStar_Syntax_Syntax.Tm_bvar (uu____17777) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____17792) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____17831) -> begin
(

let uu____17832 = (universe_of_aux env hd3)
in ((uu____17832), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____17845) -> begin
(

let uu____17846 = (universe_of_aux env hd3)
in ((uu____17846), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____17859) -> begin
(

let uu____17860 = (universe_of_aux env hd3)
in ((uu____17860), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____17873) -> begin
(

let uu____17880 = (universe_of_aux env hd3)
in ((uu____17880), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____17893) -> begin
(

let uu____17920 = (universe_of_aux env hd3)
in ((uu____17920), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____17933) -> begin
(

let uu____17940 = (universe_of_aux env hd3)
in ((uu____17940), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____17953) -> begin
(

let uu____17954 = (universe_of_aux env hd3)
in ((uu____17954), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____17967) -> begin
(

let uu____17980 = (universe_of_aux env hd3)
in ((uu____17980), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____17993) -> begin
(

let uu____18000 = (universe_of_aux env hd3)
in ((uu____18000), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____18013) -> begin
(

let uu____18014 = (universe_of_aux env hd3)
in ((uu____18014), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____18027, (hd4)::uu____18029) -> begin
(

let uu____18094 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____18094) with
| (uu____18109, uu____18110, hd5) -> begin
(

let uu____18128 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____18128) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____18179 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env e)
in (

let uu____18181 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____18181) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____18232 -> begin
(

let uu____18233 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____18233) with
| (env1, uu____18255) -> begin
(

let env2 = (

let uu___113_18261 = env1
in {FStar_TypeChecker_Env.solver = uu___113_18261.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___113_18261.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___113_18261.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___113_18261.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___113_18261.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___113_18261.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___113_18261.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___113_18261.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___113_18261.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___113_18261.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___113_18261.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___113_18261.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___113_18261.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___113_18261.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___113_18261.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___113_18261.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___113_18261.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___113_18261.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___113_18261.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___113_18261.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___113_18261.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___113_18261.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___113_18261.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___113_18261.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___113_18261.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___113_18261.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___113_18261.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___113_18261.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___113_18261.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___113_18261.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___113_18261.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___113_18261.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___113_18261.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___113_18261.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___113_18261.FStar_TypeChecker_Env.dep_graph})
in ((

let uu____18263 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____18263) with
| true -> begin
(

let uu____18264 = (

let uu____18265 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____18265))
in (

let uu____18266 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____18264 uu____18266)))
end
| uu____18267 -> begin
()
end));
(

let uu____18268 = (tc_term env2 hd3)
in (match (uu____18268) with
| (uu____18289, {FStar_Syntax_Syntax.eff_name = uu____18290; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____18292; FStar_Syntax_Syntax.comp_thunk = uu____18293}, g) -> begin
((

let uu____18313 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____18313 (fun a239 -> ())));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____18324 = (type_of_head true hd1 args)
in (match (uu____18324) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____18364 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____18364) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____18407 -> begin
(

let uu____18408 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____18408))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____18411, (hd1)::uu____18413) -> begin
(

let uu____18478 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____18478) with
| (uu____18481, uu____18482, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____18500, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____18547 = (universe_of_aux env e)
in (level_of_type env e uu____18547)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____18572 = (tc_binders env tps)
in (match (uu____18572) with
| (tps1, env1, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
((tps1), (env1), (us));
)
end)))


let rec type_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env t -> (

let mk_tm_type = (fun u -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____18626 = (

let uu____18627 = (FStar_Syntax_Subst.compress t)
in uu____18627.FStar_Syntax_Syntax.n)
in (match (uu____18626) with
| FStar_Syntax_Syntax.Tm_delayed (uu____18632) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____18659) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____18664 = (FStar_Syntax_Util.unfold_lazy i)
in (type_of_well_typed_term env uu____18664))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____18666 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env [] fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____18666 (fun uu____18680 -> (match (uu____18680) with
| (t1, uu____18688) -> begin
FStar_Pervasives_Native.Some (t1)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____18690; FStar_Syntax_Syntax.vars = uu____18691}, us) -> begin
(

let uu____18697 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env us fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____18697 (fun uu____18711 -> (match (uu____18711) with
| (t1, uu____18719) -> begin
FStar_Pervasives_Native.Some (t1)
end))))
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(

let uu____18721 = (tc_constant env t.FStar_Syntax_Syntax.pos sc)
in FStar_Pervasives_Native.Some (uu____18721))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____18723 = (mk_tm_type (FStar_Syntax_Syntax.U_succ (u)))
in FStar_Pervasives_Native.Some (uu____18723))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = eff; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (tbody); FStar_Syntax_Syntax.residual_flags = uu____18728})) -> begin
(

let mk_comp = (

let uu____18768 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____18768) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_Total')
end
| uu____18795 -> begin
(

let uu____18796 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____18796) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_GTotal')
end
| uu____18819 -> begin
FStar_Pervasives_Native.None
end))
end))
in (FStar_Util.bind_opt mk_comp (fun f -> (

let uu____18859 = (universe_of_well_typed_term env tbody)
in (FStar_Util.bind_opt uu____18859 (fun u -> (

let uu____18867 = (

let uu____18870 = (

let uu____18877 = (

let uu____18878 = (

let uu____18891 = (f tbody (FStar_Pervasives_Native.Some (u)))
in ((bs), (uu____18891)))
in FStar_Syntax_Syntax.Tm_arrow (uu____18878))
in (FStar_Syntax_Syntax.mk uu____18877))
in (uu____18870 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in FStar_Pervasives_Native.Some (uu____18867))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____18925 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____18925) with
| (bs1, c1) -> begin
(

let rec aux = (fun env1 us bs2 -> (match (bs2) with
| [] -> begin
(

let uu____18978 = (universe_of_well_typed_term env1 (FStar_Syntax_Util.comp_result c1))
in (FStar_Util.bind_opt uu____18978 (fun uc -> (

let uu____18986 = (mk_tm_type (FStar_Syntax_Syntax.U_max ((uc)::us)))
in FStar_Pervasives_Native.Some (uu____18986)))))
end
| ((x, imp))::bs3 -> begin
(

let uu____19004 = (universe_of_well_typed_term env1 x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____19004 (fun u_x -> (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x)
in (aux env2 ((u_x)::us) bs3)))))
end))
in (aux env [] bs1))
end))
end
| FStar_Syntax_Syntax.Tm_abs (uu____19013) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____19031) -> begin
(

let uu____19036 = (universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____19036 (fun u_x -> (

let uu____19044 = (mk_tm_type u_x)
in FStar_Pervasives_Native.Some (uu____19044)))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let t_hd = (type_of_well_typed_term env hd1)
in (

let rec aux = (fun t_hd1 -> (

let uu____19086 = (

let uu____19087 = (FStar_TypeChecker_Normalize.unfold_whnf env t_hd1)
in uu____19087.FStar_Syntax_Syntax.n)
in (match (uu____19086) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_bs = (FStar_List.length bs)
in (

let bs_t_opt = (match ((n_args < n_bs)) with
| true -> begin
(

let uu____19157 = (FStar_Util.first_N n_args bs)
in (match (uu____19157) with
| (bs1, rest) -> begin
(

let t1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None t_hd1.FStar_Syntax_Syntax.pos)
in (

let uu____19231 = (

let uu____19236 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Subst.open_comp bs1 uu____19236))
in (match (uu____19231) with
| (bs2, c1) -> begin
FStar_Pervasives_Native.Some (((bs2), ((FStar_Syntax_Util.comp_result c1))))
end)))
end))
end
| uu____19259 -> begin
(match ((Prims.op_Equality n_args n_bs)) with
| true -> begin
(

let uu____19280 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____19280) with
| (bs1, c1) -> begin
(

let uu____19299 = (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
in (match (uu____19299) with
| true -> begin
FStar_Pervasives_Native.Some (((bs1), ((FStar_Syntax_Util.comp_result c1))))
end
| uu____19320 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| uu____19331 -> begin
FStar_Pervasives_Native.None
end)
end)
in (FStar_Util.bind_opt bs_t_opt (fun uu____19357 -> (match (uu____19357) with
| (bs1, t1) -> begin
(

let subst1 = (FStar_List.map2 (fun b a -> FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), ((FStar_Pervasives_Native.fst a))))) bs1 args)
in (

let uu____19415 = (FStar_Syntax_Subst.subst subst1 t1)
in FStar_Pervasives_Native.Some (uu____19415)))
end))))))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____19417) -> begin
(aux x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____19423, uu____19424) -> begin
(aux t1)
end
| uu____19465 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_Util.bind_opt t_hd aux)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____19466, (FStar_Util.Inl (t1), uu____19468), uu____19469) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____19516, (FStar_Util.Inr (c), uu____19518), uu____19519) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
FStar_Pervasives_Native.Some (u.FStar_Syntax_Syntax.ctx_uvar_typ)
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.t_term)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____19574) -> begin
(type_of_well_typed_term env t1)
end
| FStar_Syntax_Syntax.Tm_match (uu____19579) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____19602) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (uu____19615) -> begin
FStar_Pervasives_Native.None
end))))
and universe_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun env t -> (

let uu____19626 = (type_of_well_typed_term env t)
in (match (uu____19626) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.pos = uu____19632; FStar_Syntax_Syntax.vars = uu____19633}) -> begin
FStar_Pervasives_Native.Some (u)
end
| uu____19636 -> begin
FStar_Pervasives_Native.None
end)))


let check_type_of_well_typed_term : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun must_total env t k -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let env2 = (

let uu___114_19661 = env1
in {FStar_TypeChecker_Env.solver = uu___114_19661.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_19661.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_19661.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_19661.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___114_19661.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___114_19661.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_19661.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_19661.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_19661.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_19661.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_19661.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_19661.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_19661.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_19661.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_19661.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_19661.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_19661.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___114_19661.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_19661.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___114_19661.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_19661.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___114_19661.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___114_19661.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___114_19661.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___114_19661.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_19661.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___114_19661.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___114_19661.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___114_19661.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___114_19661.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___114_19661.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___114_19661.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___114_19661.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___114_19661.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___114_19661.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___114_19661.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___114_19661.FStar_TypeChecker_Env.dep_graph})
in (

let slow_check = (fun uu____19667 -> (match (must_total) with
| true -> begin
(

let uu____19668 = (env2.FStar_TypeChecker_Env.type_of env2 t)
in (match (uu____19668) with
| (uu____19675, uu____19676, g) -> begin
g
end))
end
| uu____19678 -> begin
(

let uu____19679 = (env2.FStar_TypeChecker_Env.tc_term env2 t)
in (match (uu____19679) with
| (uu____19686, uu____19687, g) -> begin
g
end))
end))
in (

let uu____19689 = (

let uu____19690 = (FStar_Options.__temp_fast_implicits ())
in (FStar_All.pipe_left Prims.op_Negation uu____19690))
in (match (uu____19689) with
| true -> begin
(slow_check ())
end
| uu____19691 -> begin
(

let uu____19692 = (type_of_well_typed_term env2 t)
in (match (uu____19692) with
| FStar_Pervasives_Native.None -> begin
(slow_check ())
end
| FStar_Pervasives_Native.Some (k') -> begin
((

let uu____19697 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____19697) with
| true -> begin
(

let uu____19698 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____19699 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____19700 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____19701 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n" uu____19698 uu____19699 uu____19700 uu____19701)))))
end
| uu____19702 -> begin
()
end));
(

let b = (FStar_TypeChecker_Rel.subtype_nosmt env2 k' k)
in ((

let uu____19705 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____19705) with
| true -> begin
(

let uu____19706 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____19707 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____19708 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____19709 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n" uu____19706 (match (b) with
| true -> begin
"succeeded"
end
| uu____19710 -> begin
"failed"
end) uu____19707 uu____19708 uu____19709)))))
end
| uu____19711 -> begin
()
end));
(match (b) with
| true -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____19712 -> begin
(slow_check ())
end);
));
)
end))
end))))))




