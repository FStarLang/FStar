
open Prims
open FStar_Pervasives

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___70_6 = env
in {FStar_TypeChecker_Env.solver = uu___70_6.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___70_6.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___70_6.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___70_6.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___70_6.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___70_6.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___70_6.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___70_6.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___70_6.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___70_6.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___70_6.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___70_6.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___70_6.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___70_6.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___70_6.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___70_6.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___70_6.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___70_6.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___70_6.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___70_6.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___70_6.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___70_6.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___70_6.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___70_6.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___70_6.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___70_6.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___70_6.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___70_6.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___70_6.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___70_6.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___70_6.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___70_6.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___70_6.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___70_6.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___70_6.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___70_6.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___70_6.FStar_TypeChecker_Env.dep_graph}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___71_12 = env
in {FStar_TypeChecker_Env.solver = uu___71_12.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___71_12.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___71_12.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___71_12.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___71_12.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___71_12.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___71_12.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___71_12.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___71_12.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___71_12.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___71_12.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___71_12.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___71_12.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___71_12.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___71_12.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___71_12.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___71_12.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___71_12.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___71_12.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___71_12.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___71_12.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___71_12.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___71_12.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___71_12.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___71_12.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___71_12.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___71_12.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___71_12.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___71_12.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___71_12.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___71_12.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___71_12.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___71_12.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___71_12.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___71_12.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___71_12.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___71_12.FStar_TypeChecker_Env.dep_graph}))


let mk_lex_list : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term = (fun vs -> (FStar_List.fold_right (fun v1 tl1 -> (

let r = (match ((Prims.op_Equality tl1.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
v1.FStar_Syntax_Syntax.pos
end
| uu____39 -> begin
(FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos tl1.FStar_Syntax_Syntax.pos)
end)
in (

let uu____40 = (

let uu____45 = (

let uu____46 = (FStar_Syntax_Syntax.as_arg v1)
in (

let uu____53 = (

let uu____62 = (FStar_Syntax_Syntax.as_arg tl1)
in (uu____62)::[])
in (uu____46)::uu____53))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____45))
in (uu____40 FStar_Pervasives_Native.None r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___65_95 -> (match (uu___65_95) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____98 -> begin
false
end))


let steps : 'Auu____105 . 'Auu____105  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[])


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
((t), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____188 -> begin
(

let t1 = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____192 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t1)
in (

let uu____196 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____196) with
| FStar_Pervasives_Native.None -> begin
((t1), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t1)
end
| uu____210 -> begin
(

let fail1 = (fun uu____220 -> (

let msg = (match (head_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____222 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" uu____222))
end
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____224 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____225 = (FStar_TypeChecker_Normalize.term_to_string env head1)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" uu____224 uu____225)))
end)
in (

let uu____226 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_EscapedBoundVar), (msg)) uu____226))))
in (

let uu____231 = (

let uu____244 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____245 = (

let uu____246 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____246))
in (FStar_TypeChecker_Util.new_implicit_var "no escape" uu____244 env uu____245)))
in (match (uu____231) with
| (s, uu____260, g0) -> begin
(

let uu____274 = (FStar_TypeChecker_Rel.try_teq true env t1 s)
in (match (uu____274) with
| FStar_Pervasives_Native.Some (g) -> begin
(

let g1 = (

let uu____283 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____283))
in ((s), (g1)))
end
| uu____284 -> begin
(fail1 ())
end))
end)))
end)
end))))
end))
in (aux false kt)))


let push_binding : 'Auu____293 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____293)  ->  FStar_TypeChecker_Env.env = (fun env b -> (FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v1 -> (

let uu____343 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____343) with
| true -> begin
s
end
| uu____344 -> begin
(FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), (v1))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags (fun uu____363 -> (

let uu____364 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Util.set_result_typ uu____364 t)))))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> e)


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____419 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____419))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____424 = (

let uu____431 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____431) with
| FStar_Pervasives_Native.None -> begin
(((memo_tk e t)), (lc), (guard))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____441 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____441) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____457 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____457) with
| (e2, g) -> begin
((

let uu____471 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____471) with
| true -> begin
(

let uu____472 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____473 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____474 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____475 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____472 uu____473 uu____474 uu____475)))))
end
| uu____476 -> begin
()
end));
(

let msg = (

let uu____483 = (FStar_TypeChecker_Rel.is_trivial g)
in (match (uu____483) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____492 -> begin
(FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____505 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc1 g1)
in (match (uu____505) with
| (lc2, g2) -> begin
(

let uu____518 = (set_lcomp_result lc2 t')
in (((memo_tk e2 t')), (uu____518), (g2)))
end))));
)
end)))
end))
end))
in (match (uu____424) with
| (e1, lc1, g) -> begin
((e1), (lc1), (g))
end)))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____555 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____555) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____565 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____565) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt ec -> (

let uu____617 = ec
in (match (uu____617) with
| (e, c) -> begin
(

let tot_or_gtot = (fun c1 -> (

let uu____640 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____640) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c1))
end
| uu____641 -> begin
(

let uu____642 = (FStar_Syntax_Util.is_pure_or_ghost_comp c1)
in (match (uu____642) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c1))
end
| uu____643 -> begin
(failwith "Impossible: Expected pure_or_ghost comp")
end))
end)))
in (

let uu____644 = (match (copt) with
| FStar_Pervasives_Native.Some (uu____657) -> begin
((copt), (c))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____660 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Parser_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____662 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____662)))))
in (match (uu____660) with
| true -> begin
(

let uu____669 = (

let uu____672 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____672))
in ((uu____669), (c)))
end
| uu____675 -> begin
(

let uu____676 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____676) with
| true -> begin
(

let uu____683 = (tot_or_gtot c)
in ((FStar_Pervasives_Native.None), (uu____683)))
end
| uu____686 -> begin
(

let uu____687 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____687) with
| true -> begin
(

let uu____694 = (

let uu____697 = (tot_or_gtot c)
in FStar_Pervasives_Native.Some (uu____697))
in ((uu____694), (c)))
end
| uu____700 -> begin
((FStar_Pervasives_Native.None), (c))
end))
end))
end))
end)
in (match (uu____644) with
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

let uu____724 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e uu____724))
in (

let c4 = (FStar_Syntax_Syntax.lcomp_comp c3)
in (

let uu____726 = (FStar_TypeChecker_Util.check_comp env e c4 expected_c)
in (match (uu____726) with
| (e1, uu____740, g) -> begin
(

let g1 = (

let uu____743 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____743 "could not prove post-condition" g))
in ((

let uu____745 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____745) with
| true -> begin
(

let uu____746 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____747 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" uu____746 uu____747)))
end
| uu____748 -> begin
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


let no_logical_guard : 'Auu____758 'Auu____759 . FStar_TypeChecker_Env.env  ->  ('Auu____758 * 'Auu____759 * FStar_TypeChecker_Env.guard_t)  ->  ('Auu____758 * 'Auu____759 * FStar_TypeChecker_Env.guard_t) = (fun env uu____781 -> (match (uu____781) with
| (te, kt, f) -> begin
(

let uu____791 = (FStar_TypeChecker_Rel.guard_form f)
in (match (uu____791) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____799 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____804 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____799 uu____804)))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let uu____816 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____816) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "Expected type is None\n")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____820 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____820))
end)))


let rec get_pat_vars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun pats acc -> (

let pats1 = (FStar_Syntax_Util.unmeta pats)
in (

let uu____852 = (FStar_Syntax_Util.head_and_args pats1)
in (match (uu____852) with
| (head1, args) -> begin
(

let uu____891 = (

let uu____892 = (FStar_Syntax_Util.un_uinst head1)
in uu____892.FStar_Syntax_Syntax.n)
in (match (uu____891) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
acc
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
(

let uu____899 = (FStar_List.tl args)
in (get_pat_vars_args uu____899 acc))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
(get_pat_vars_args args acc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(get_pat_vars_args args acc)
end
| uu____908 -> begin
(

let uu____909 = (FStar_Syntax_Free.names pats1)
in (FStar_Util.set_union acc uu____909))
end))
end))))
and get_pat_vars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun args acc -> (FStar_List.fold_left (fun s arg -> (get_pat_vars (FStar_Pervasives_Native.fst arg) s)) acc args))


let check_smt_pat : 'Auu____944 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * 'Auu____944) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  unit = (fun env t bs c -> (

let uu____985 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____985) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____986; FStar_Syntax_Syntax.effect_name = uu____987; FStar_Syntax_Syntax.result_typ = uu____988; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____992))::[]; FStar_Syntax_Syntax.flags = uu____993}) -> begin
(

let pat_vars = (

let uu____1041 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (

let uu____1042 = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
in (get_pat_vars uu____1041 uu____1042)))
in (

let uu____1045 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____1072 -> (match (uu____1072) with
| (b, uu____1078) -> begin
(

let uu____1079 = (FStar_Util.set_mem b pat_vars)
in (not (uu____1079)))
end))))
in (match (uu____1045) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____1085) -> begin
(

let uu____1090 = (

let uu____1095 = (

let uu____1096 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____1096))
in ((FStar_Errors.Warning_PatternMissingBoundVar), (uu____1095)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1090))
end)))
end
| uu____1097 -> begin
(failwith "Impossible")
end)
end
| uu____1098 -> begin
()
end)))


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.univ_names) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env1 = (

let uu___72_1153 = env
in {FStar_TypeChecker_Env.solver = uu___72_1153.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___72_1153.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___72_1153.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___72_1153.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___72_1153.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___72_1153.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___72_1153.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___72_1153.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___72_1153.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___72_1153.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___72_1153.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___72_1153.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___72_1153.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___72_1153.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___72_1153.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___72_1153.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___72_1153.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___72_1153.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___72_1153.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___72_1153.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___72_1153.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___72_1153.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___72_1153.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___72_1153.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___72_1153.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___72_1153.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___72_1153.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___72_1153.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___72_1153.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___72_1153.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___72_1153.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___72_1153.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___72_1153.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___72_1153.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___72_1153.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___72_1153.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___72_1153.FStar_TypeChecker_Env.dep_graph})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> ((

let uu____1173 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1173) with
| true -> begin
(

let uu____1174 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (

let uu____1175 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "Building a decreases clause over (%s) and %s\n" uu____1174 uu____1175)))
end
| uu____1176 -> begin
()
end));
(

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____1202 -> (match (uu____1202) with
| (b, uu____1210) -> begin
(

let t = (

let uu____1212 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____1212))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____1215) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1216) -> begin
[]
end
| uu____1229 -> begin
(

let uu____1230 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____1230)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____1237 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____1237) with
| (head1, uu____1253) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____1275 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____1283 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___66_1292 -> (match (uu___66_1292) with
| FStar_Syntax_Syntax.DECREASES (uu____1293) -> begin
true
end
| uu____1296 -> begin
false
end))))
in (match (uu____1283) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____1300 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____1319 -> begin
(mk_lex_list xs)
end))
end)))));
))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____1344 -> (match (uu____1344) with
| (l, t, u_names) -> begin
(

let uu____1362 = (

let uu____1363 = (FStar_Syntax_Subst.compress t)
in uu____1363.FStar_Syntax_Syntax.n)
in (match (uu____1362) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____1412 -> (match (uu____1412) with
| (x, imp) -> begin
(

let uu____1423 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____1423) with
| true -> begin
(

let uu____1428 = (

let uu____1429 = (

let uu____1432 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____1432))
in (FStar_Syntax_Syntax.new_bv uu____1429 x.FStar_Syntax_Syntax.sort))
in ((uu____1428), (imp)))
end
| uu____1433 -> begin
((x), (imp))
end))
end))))
in (

let uu____1434 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____1434) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____1453 = (

let uu____1458 = (

let uu____1459 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____1466 = (

let uu____1475 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____1475)::[])
in (uu____1459)::uu____1466))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____1458))
in (uu____1453 FStar_Pervasives_Native.None r))
in (

let uu____1502 = (FStar_Util.prefix formals2)
in (match (uu____1502) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___73_1549 = last1
in (

let uu____1550 = (FStar_Syntax_Util.refine last1 precedes1)
in {FStar_Syntax_Syntax.ppname = uu___73_1549.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___73_1549.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1550}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____1576 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1576) with
| true -> begin
(

let uu____1577 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____1578 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1579 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____1577 uu____1578 uu____1579))))
end
| uu____1580 -> begin
()
end));
((l), (t'), (u_names));
))))
end))))
end)))
end
| uu____1583 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectedArrowAnnotatedType), ("Annotated type of \'let rec\' must be an arrow")) t.FStar_Syntax_Syntax.pos)
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let uu___74_2179 = env
in {FStar_TypeChecker_Env.solver = uu___74_2179.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___74_2179.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___74_2179.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___74_2179.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___74_2179.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___74_2179.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___74_2179.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___74_2179.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___74_2179.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___74_2179.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___74_2179.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___74_2179.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___74_2179.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___74_2179.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___74_2179.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___74_2179.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___74_2179.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___74_2179.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___74_2179.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___74_2179.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___74_2179.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___74_2179.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___74_2179.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___74_2179.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___74_2179.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___74_2179.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___74_2179.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___74_2179.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___74_2179.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___74_2179.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___74_2179.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___74_2179.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___74_2179.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___74_2179.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___74_2179.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___74_2179.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___74_2179.FStar_TypeChecker_Env.dep_graph}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (match ((Prims.op_Equality e.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____2189 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____2191 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____2191) with
| true -> begin
(

let uu____2192 = (

let uu____2193 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2193))
in (

let uu____2194 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" uu____2192 uu____2194)))
end
| uu____2195 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2203) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2234) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2241) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2242) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____2243) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2244) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____2245) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____2246) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2263) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____2276) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____2283) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____2284, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aqs}) when (FStar_List.for_all (fun uu____2312 -> (match (uu____2312) with
| (uu____2321, b, uu____2323) -> begin
(not (b))
end)) aqs) -> begin
(value_check_expected_typ env1 top (FStar_Util.Inl (FStar_Syntax_Syntax.t_term)) FStar_TypeChecker_Rel.trivial_guard)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____2328) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Tac_lid; FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_term; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.SOMETRIVIAL)::(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]})
in (

let uu____2342 = (

let uu____2349 = (

let uu____2354 = (FStar_Syntax_Util.lcomp_of_comp c)
in FStar_Util.Inr (uu____2354))
in (value_check_expected_typ env1 top uu____2349 FStar_TypeChecker_Rel.trivial_guard))
in (match (uu____2342) with
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

let uu____2377 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____2377) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___75_2394 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___75_2394.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___75_2394.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___75_2394.FStar_TypeChecker_Env.implicits})
in (

let uu____2395 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____2395), (c), (g1))))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____2414 = (FStar_Syntax_Util.type_u ())
in (match (uu____2414) with
| (t, u) -> begin
(

let uu____2427 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____2427) with
| (e2, c, g) -> begin
(

let uu____2443 = (

let uu____2458 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2458) with
| (env2, uu____2480) -> begin
(tc_pats env2 pats)
end))
in (match (uu____2443) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___76_2514 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___76_2514.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___76_2514.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___76_2514.FStar_TypeChecker_Env.implicits})
in (

let uu____2515 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2518 = (FStar_TypeChecker_Rel.conj_guard g g'1)
in ((uu____2515), (c), (uu____2518)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____2524 = (

let uu____2525 = (FStar_Syntax_Subst.compress e1)
in uu____2525.FStar_Syntax_Syntax.n)
in (match (uu____2524) with
| FStar_Syntax_Syntax.Tm_let ((uu____2534, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____2536; FStar_Syntax_Syntax.lbtyp = uu____2537; FStar_Syntax_Syntax.lbeff = uu____2538; FStar_Syntax_Syntax.lbdef = e11; FStar_Syntax_Syntax.lbattrs = uu____2540; FStar_Syntax_Syntax.lbpos = uu____2541})::[]), e2) -> begin
(

let uu____2569 = (

let uu____2576 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (tc_term uu____2576 e11))
in (match (uu____2569) with
| (e12, c1, g1) -> begin
(

let uu____2586 = (tc_term env1 e2)
in (match (uu____2586) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.maybe_return_e2_and_bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 e21 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e3 = (

let uu____2610 = (

let uu____2617 = (

let uu____2618 = (

let uu____2631 = (

let uu____2638 = (

let uu____2641 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_Syntax_Syntax.t_unit), (e13), (e13.FStar_Syntax_Syntax.pos)))
in (uu____2641)::[])
in ((false), (uu____2638)))
in ((uu____2631), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____2618))
in (FStar_Syntax_Syntax.mk uu____2617))
in (uu____2610 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2663 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e5), (c), (uu____2663)))))))))
end))
end))
end
| uu____2664 -> begin
(

let uu____2665 = (tc_term env1 e1)
in (match (uu____2665) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____2687)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic_lift (uu____2699)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____2718 = (tc_term env1 e1)
in (match (uu____2718) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____2742) -> begin
(

let uu____2789 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2789) with
| (env0, uu____2803) -> begin
(

let uu____2808 = (tc_comp env0 expected_c)
in (match (uu____2808) with
| (expected_c1, uu____2822, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c1)
in (

let uu____2827 = (

let uu____2834 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____2834 e1))
in (match (uu____2827) with
| (e2, c', g') -> begin
(

let uu____2844 = (

let uu____2851 = (

let uu____2856 = (FStar_Syntax_Syntax.lcomp_comp c')
in ((e2), (uu____2856)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____2851))
in (match (uu____2844) with
| (e3, expected_c2, g'') -> begin
(

let topt1 = (tc_tactic_opt env0 topt)
in (

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inr (expected_c2)), (topt1))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____2904 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____2904))
in (

let f1 = (match (topt1) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(FStar_TypeChecker_Rel.map_guard f (fun f1 -> (

let uu____2910 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero f1)
in (FStar_TypeChecker_Common.mk_by_tactic tactic uu____2910))))
end)
in (

let uu____2911 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____2911) with
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
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____2931) -> begin
(

let uu____2978 = (FStar_Syntax_Util.type_u ())
in (match (uu____2978) with
| (k, u) -> begin
(

let uu____2991 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____2991) with
| (t1, uu____3005, f) -> begin
(

let uu____3007 = (

let uu____3014 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____3014 e1))
in (match (uu____3007) with
| (e2, c, g) -> begin
(

let uu____3024 = (

let uu____3029 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____3034 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____3029 e2 c f))
in (match (uu____3024) with
| (c1, f1) -> begin
(

let uu____3043 = (

let uu____3050 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____3050 c1))
in (match (uu____3043) with
| (e3, c2, f2) -> begin
(

let uu____3094 = (

let uu____3095 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____3095))
in ((e3), (c2), (uu____3094)))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____3096; FStar_Syntax_Syntax.vars = uu____3097}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3160 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3160) with
| (unary_op, uu____3182) -> begin
(

let head1 = (

let uu____3206 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____3206))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____3244; FStar_Syntax_Syntax.vars = uu____3245}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3308 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3308) with
| (unary_op, uu____3330) -> begin
(

let head1 = (

let uu____3354 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____3354))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3392)); FStar_Syntax_Syntax.pos = uu____3393; FStar_Syntax_Syntax.vars = uu____3394}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3457 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3457) with
| (unary_op, uu____3479) -> begin
(

let head1 = (

let uu____3503 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____3503))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____3541; FStar_Syntax_Syntax.vars = uu____3542}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3618 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3618) with
| (unary_op, uu____3640) -> begin
(

let head1 = (

let uu____3664 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a1)::(a2)::[])))) FStar_Pervasives_Native.None uu____3664))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____3708; FStar_Syntax_Syntax.vars = uu____3709}, ((e1, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____3739 = (

let uu____3746 = (

let uu____3747 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3747))
in (tc_term uu____3746 e1))
in (match (uu____3739) with
| (e2, c, g) -> begin
(

let uu____3771 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3771) with
| (head1, uu____3793) -> begin
(

let uu____3814 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((((e2), (FStar_Pervasives_Native.None)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3839 = (

let uu____3840 = (

let uu____3841 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_Syntax_Syntax.mk_Total uu____3841))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3840))
in ((uu____3814), (uu____3839), (g))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____3842; FStar_Syntax_Syntax.vars = uu____3843}, ((t, FStar_Pervasives_Native.None))::((r, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____3884 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3884) with
| (head1, uu____3906) -> begin
(

let env' = (

let uu____3928 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_TypeChecker_Env.set_expected_typ env1 uu____3928))
in (

let uu____3929 = (tc_term env' r)
in (match (uu____3929) with
| (er, uu____3943, gr) -> begin
(

let uu____3945 = (tc_term env1 t)
in (match (uu____3945) with
| (t1, tt, gt1) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard gr gt1)
in (

let uu____3962 = (

let uu____3963 = (

let uu____3968 = (

let uu____3969 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3976 = (

let uu____3985 = (FStar_Syntax_Syntax.as_arg r)
in (uu____3985)::[])
in (uu____3969)::uu____3976))
in (FStar_Syntax_Syntax.mk_Tm_app head1 uu____3968))
in (uu____3963 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in ((uu____3962), (tt), (g))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____4012; FStar_Syntax_Syntax.vars = uu____4013}, uu____4014) -> begin
(

let uu____4035 = (

let uu____4040 = (

let uu____4041 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____4041))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____4040)))
in (FStar_Errors.raise_error uu____4035 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____4048; FStar_Syntax_Syntax.vars = uu____4049}, uu____4050) -> begin
(

let uu____4071 = (

let uu____4076 = (

let uu____4077 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____4077))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____4076)))
in (FStar_Errors.raise_error uu____4071 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4084; FStar_Syntax_Syntax.vars = uu____4085}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify), ("Qualifier on argument to reify is irrelevant and will be ignored")))
end
| uu____4117 -> begin
()
end);
(

let uu____4118 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4118) with
| (env0, uu____4132) -> begin
(

let uu____4137 = (tc_term env0 e1)
in (match (uu____4137) with
| (e2, c, g) -> begin
(

let uu____4153 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4153) with
| (reify_op, uu____4175) -> begin
(

let u_c = (

let uu____4197 = (tc_term env0 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____4197) with
| (uu____4204, c', uu____4206) -> begin
(

let uu____4207 = (

let uu____4208 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____4208.FStar_Syntax_Syntax.n)
in (match (uu____4207) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____4212 -> begin
(

let uu____4213 = (FStar_Syntax_Util.type_u ())
in (match (uu____4213) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4225 = (

let uu____4226 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____4227 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____4228 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____4226 uu____4227 uu____4228))))
in (failwith uu____4225))
end);
u;
))
end))
end))
end))
in (

let repr = (

let uu____4230 = (FStar_Syntax_Syntax.lcomp_comp c)
in (FStar_TypeChecker_Env.reify_comp env1 uu____4230 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____4253 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____4253 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____4254 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____4254) with
| (e4, c2, g') -> begin
(

let uu____4270 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e4), (c2), (uu____4270)))
end))))))
end))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.pos = uu____4272; FStar_Syntax_Syntax.vars = uu____4273}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect), ("Qualifier on argument to reflect is irrelevant and will be ignored")))
end
| uu____4305 -> begin
()
end);
(

let no_reflect = (fun uu____4317 -> (

let uu____4318 = (

let uu____4323 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____4323)))
in (FStar_Errors.raise_error uu____4318 e1.FStar_Syntax_Syntax.pos)))
in (

let uu____4330 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4330) with
| (reflect_op, uu____4352) -> begin
(

let uu____4373 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____4373) with
| FStar_Pervasives_Native.None -> begin
(no_reflect ())
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____4406 = (

let uu____4407 = (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____4407)))
in (match (uu____4406) with
| true -> begin
(no_reflect ())
end
| uu____4416 -> begin
(

let uu____4417 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4417) with
| (env_no_ex, topt) -> begin
(

let uu____4436 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____4458 = (

let uu____4465 = (

let uu____4466 = (

let uu____4481 = (

let uu____4490 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____4491 = (

let uu____4494 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____4494)::[])
in (uu____4490)::uu____4491))
in ((repr), (uu____4481)))
in FStar_Syntax_Syntax.Tm_app (uu____4466))
in (FStar_Syntax_Syntax.mk uu____4465))
in (uu____4458 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____4508 = (

let uu____4515 = (

let uu____4516 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____4516 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____4515 t))
in (match (uu____4508) with
| (t1, uu____4544, g) -> begin
(

let uu____4546 = (

let uu____4547 = (FStar_Syntax_Subst.compress t1)
in uu____4547.FStar_Syntax_Syntax.n)
in (match (uu____4546) with
| FStar_Syntax_Syntax.Tm_app (uu____4562, ((res, uu____4564))::((wp, uu____4566))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____4609 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____4436) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____4640 = (

let uu____4645 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____4645) with
| (e2, c, g) -> begin
((

let uu____4660 = (

let uu____4661 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____4661))
in (match (uu____4660) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 ((((FStar_Errors.Error_UnexpectedGTotComputation), ("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____4674 -> begin
()
end));
(

let uu____4675 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____4675) with
| FStar_Pervasives_Native.None -> begin
((

let uu____4683 = (

let uu____4692 = (

let uu____4699 = (

let uu____4700 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____4701 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____4700 uu____4701)))
in ((FStar_Errors.Error_UnexpectedInstance), (uu____4699), (e2.FStar_Syntax_Syntax.pos)))
in (uu____4692)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____4683));
(

let uu____4714 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e2), (uu____4714)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____4716 = (

let uu____4717 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____4717))
in ((e2), (uu____4716)))
end));
)
end))
in (match (uu____4640) with
| (e2, g) -> begin
(

let c = (

let uu____4727 = (

let uu____4728 = (

let uu____4729 = (

let uu____4730 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____4730)::[])
in (

let uu____4731 = (

let uu____4740 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4740)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____4729; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____4731; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____4728))
in (FStar_All.pipe_right uu____4727 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____4780 = (comp_check_expected_typ env1 e3 c)
in (match (uu____4780) with
| (e4, c1, g') -> begin
(

let uu____4796 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e4), (c1), (uu____4796)))
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

let uu____4843 = (

let uu____4844 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____4844 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____4843 instantiate_both))
in ((

let uu____4860 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____4860) with
| true -> begin
(

let uu____4861 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____4862 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____4861 uu____4862)))
end
| uu____4863 -> begin
()
end));
(

let uu____4864 = (tc_term (no_inst env2) head1)
in (match (uu____4864) with
| (head2, chead, g_head) -> begin
(

let uu____4880 = (

let uu____4887 = (((not (env2.FStar_TypeChecker_Env.lax)) && (

let uu____4889 = (FStar_Options.lax ())
in (not (uu____4889)))) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____4887) with
| true -> begin
(

let uu____4896 = (

let uu____4903 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____4903))
in (match (uu____4896) with
| (e1, c, g) -> begin
((e1), (c), (g))
end))
end
| uu____4915 -> begin
(

let uu____4916 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env2 head2 chead g_head args uu____4916))
end))
in (match (uu____4880) with
| (e1, c, g) -> begin
((

let uu____4929 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____4929) with
| true -> begin
(

let uu____4930 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____4930))
end
| uu____4931 -> begin
()
end));
(

let uu____4932 = (comp_check_expected_typ env0 e1 c)
in (match (uu____4932) with
| (e2, c1, g') -> begin
(

let gres = (FStar_TypeChecker_Rel.conj_guard g g')
in ((

let uu____4950 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____4950) with
| true -> begin
(

let uu____4951 = (FStar_Syntax_Print.term_to_string e2)
in (

let uu____4952 = (FStar_TypeChecker_Rel.guard_to_string env2 gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____4951 uu____4952)))
end
| uu____4953 -> begin
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

let uu____4992 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4992) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____5012 = (tc_term env12 e1)
in (match (uu____5012) with
| (e11, c1, g1) -> begin
(

let uu____5028 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t), (g1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5042 = (FStar_Syntax_Util.type_u ())
in (match (uu____5042) with
| (k, uu____5054) -> begin
(

let uu____5055 = (FStar_TypeChecker_Util.new_implicit_var "match result" e.FStar_Syntax_Syntax.pos env1 k)
in (match (uu____5055) with
| (res_t, uu____5075, g) -> begin
(

let uu____5089 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in (

let uu____5090 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in ((uu____5089), (res_t), (uu____5090))))
end))
end))
end)
in (match (uu____5028) with
| (env_branches, res_t, g11) -> begin
((

let uu____5101 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____5101) with
| true -> begin
(

let uu____5102 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____5102))
end
| uu____5103 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____5223 = (

let uu____5228 = (FStar_List.fold_right (fun uu____5307 uu____5308 -> (match (((uu____5307), (uu____5308))) with
| ((branch1, f, eff_label, cflags, c, g), (caccum, gaccum)) -> begin
(

let uu____5542 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (eff_label), (cflags), (c)))::caccum), (uu____5542)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____5228) with
| (cases, g) -> begin
(

let uu____5640 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____5640), (g)))
end))
in (match (uu____5223) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____5782 -> (match (uu____5782) with
| ((pat, wopt, br), uu____5826, eff_label, uu____5828, uu____5829, uu____5830) -> begin
(

let uu____5865 = (FStar_TypeChecker_Util.maybe_lift env1 br eff_label cres.FStar_Syntax_Syntax.eff_name res_t)
in ((pat), (wopt), (uu____5865)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____5932 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____5932) with
| true -> begin
(mk_match e11)
end
| uu____5935 -> begin
(

let e_match = (

let uu____5939 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____5939))
in (

let lb = (

let uu____5943 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (guard_x)) [] c1.FStar_Syntax_Syntax.res_typ uu____5943 e11 [] e11.FStar_Syntax_Syntax.pos))
in (

let e2 = (

let uu____5949 = (

let uu____5956 = (

let uu____5957 = (

let uu____5970 = (

let uu____5973 = (

let uu____5974 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____5974)::[])
in (FStar_Syntax_Subst.close uu____5973 e_match))
in ((((false), ((lb)::[]))), (uu____5970)))
in FStar_Syntax_Syntax.Tm_let (uu____5957))
in (FStar_Syntax_Syntax.mk uu____5956))
in (uu____5949 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____6001 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____6001) with
| true -> begin
(

let uu____6002 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____6003 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____6002 uu____6003)))
end
| uu____6004 -> begin
()
end));
(

let uu____6005 = (FStar_TypeChecker_Rel.conj_guard g11 g_branches)
in ((e2), (cres), (uu____6005)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____6006); FStar_Syntax_Syntax.lbunivs = uu____6007; FStar_Syntax_Syntax.lbtyp = uu____6008; FStar_Syntax_Syntax.lbeff = uu____6009; FStar_Syntax_Syntax.lbdef = uu____6010; FStar_Syntax_Syntax.lbattrs = uu____6011; FStar_Syntax_Syntax.lbpos = uu____6012})::[]), uu____6013) -> begin
(check_top_level_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____6036), uu____6037) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____6052); FStar_Syntax_Syntax.lbunivs = uu____6053; FStar_Syntax_Syntax.lbtyp = uu____6054; FStar_Syntax_Syntax.lbeff = uu____6055; FStar_Syntax_Syntax.lbdef = uu____6056; FStar_Syntax_Syntax.lbattrs = uu____6057; FStar_Syntax_Syntax.lbpos = uu____6058})::uu____6059), uu____6060) -> begin
(check_top_level_let_rec env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____6085), uu____6086) -> begin
(check_inner_let_rec env1 top)
end));
)))
and tc_synth : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env args rng -> (

let uu____6112 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.None), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6182))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.Some (a)), (rest))
end
| uu____6229 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: bad application")) rng)
end)
in (match (uu____6112) with
| (tau, atyp, rest) -> begin
(

let typ = (match (atyp) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6291 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6291) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6295 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: need a type annotation when no expected type is present")) uu____6295))
end))
end)
in (

let uu____6296 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____6296) with
| (env', uu____6310) -> begin
(

let uu____6315 = (tc_term env' typ)
in (match (uu____6315) with
| (typ1, uu____6329, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g1);
(

let uu____6332 = (tc_tactic env' tau)
in (match (uu____6332) with
| (tau1, uu____6346, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g2);
(

let t = (match (env.FStar_TypeChecker_Env.nosynth) with
| true -> begin
(

let uu____6350 = (

let uu____6355 = (FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.magic_lid)
in (

let uu____6356 = (

let uu____6357 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____6357)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____6355 uu____6356)))
in (uu____6350 FStar_Pervasives_Native.None rng))
end
| uu____6378 -> begin
(

let t = (env.FStar_TypeChecker_Env.synth_hook env' typ1 tau1)
in ((

let uu____6381 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____6381) with
| true -> begin
(

let uu____6382 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____6382))
end
| uu____6383 -> begin
()
end));
t;
))
end)
in ((FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(

let uu____6385 = (FStar_Syntax_Syntax.mk_Tm_app t rest FStar_Pervasives_Native.None rng)
in (tc_term env uu____6385));
));
)
end));
)
end))
end)))
end)))
and tc_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___77_6389 = env
in {FStar_TypeChecker_Env.solver = uu___77_6389.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___77_6389.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___77_6389.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___77_6389.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___77_6389.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___77_6389.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___77_6389.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___77_6389.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___77_6389.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___77_6389.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___77_6389.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___77_6389.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___77_6389.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___77_6389.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___77_6389.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___77_6389.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___77_6389.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___77_6389.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___77_6389.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___77_6389.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___77_6389.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___77_6389.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___77_6389.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___77_6389.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___77_6389.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___77_6389.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___77_6389.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___77_6389.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___77_6389.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___77_6389.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___77_6389.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___77_6389.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___77_6389.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___77_6389.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___77_6389.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___77_6389.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___77_6389.FStar_TypeChecker_Env.dep_graph})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit)))
and tc_reified_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___78_6393 = env
in {FStar_TypeChecker_Env.solver = uu___78_6393.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___78_6393.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___78_6393.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___78_6393.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___78_6393.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___78_6393.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___78_6393.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___78_6393.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___78_6393.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___78_6393.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___78_6393.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___78_6393.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___78_6393.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___78_6393.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___78_6393.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___78_6393.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___78_6393.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___78_6393.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___78_6393.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___78_6393.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___78_6393.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___78_6393.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___78_6393.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___78_6393.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___78_6393.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___78_6393.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___78_6393.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___78_6393.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___78_6393.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___78_6393.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___78_6393.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___78_6393.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___78_6393.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___78_6393.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___78_6393.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___78_6393.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___78_6393.FStar_TypeChecker_Env.dep_graph})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____6409 = (tc_tactic env tactic)
in (match (uu____6409) with
| (tactic1, uu____6419, uu____6420) -> begin
FStar_Pervasives_Native.Some (tactic1)
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t0 -> (

let uu____6469 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0)
in (match (uu____6469) with
| (e2, t, implicits) -> begin
(

let tc = (

let uu____6490 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____6490) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____6495 -> begin
(

let uu____6496 = (

let uu____6497 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6497))
in FStar_Util.Inr (uu____6496))
end))
in (

let is_data_ctor = (fun uu___67_6505 -> (match (uu___67_6505) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6508)) -> begin
true
end
| uu____6515 -> begin
false
end))
in (

let uu____6518 = ((is_data_ctor dc) && (

let uu____6520 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____6520))))
in (match (uu____6518) with
| true -> begin
(

let uu____6527 = (

let uu____6532 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingDataConstructor), (uu____6532)))
in (

let uu____6533 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____6527 uu____6533)))
end
| uu____6540 -> begin
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

let uu____6550 = (

let uu____6551 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____6551))
in (failwith uu____6550))
end
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
(value_check_expected_typ env1 e (FStar_Util.Inl (u.FStar_Syntax_Syntax.ctx_uvar_typ)) FStar_TypeChecker_Rel.trivial_guard)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____6560 = (

let uu____6573 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____6573) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6588 = (FStar_Syntax_Util.type_u ())
in (match (uu____6588) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____6560) with
| (t, uu____6625, g0) -> begin
(

let uu____6639 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____6639) with
| (e1, uu____6659, g1) -> begin
(

let uu____6673 = (

let uu____6674 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____6674 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____6675 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e1), (uu____6673), (uu____6675))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____6677 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____6690 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____6690)))
end
| uu____6693 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____6677) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___79_6709 = x
in {FStar_Syntax_Syntax.ppname = uu___79_6709.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___79_6709.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Env.insert_bv_info env1 x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____6712 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____6712) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____6733 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____6733) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____6738 -> begin
(

let uu____6739 = (

let uu____6740 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6740))
in FStar_Util.Inr (uu____6739))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6742; FStar_Syntax_Syntax.vars = uu____6743}, uu____6744) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____6749 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____6749))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____6757 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____6757))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6765; FStar_Syntax_Syntax.vars = uu____6766}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____6775 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6775) with
| ((us', t), range) -> begin
((match ((Prims.op_disEquality (FStar_List.length us1) (FStar_List.length us'))) with
| true -> begin
(

let uu____6798 = (

let uu____6803 = (

let uu____6804 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____6805 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____6806 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____6804 uu____6805 uu____6806))))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____6803)))
in (

let uu____6807 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____6798 uu____6807)))
end
| uu____6808 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____6823 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____6827 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6827 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____6829 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6829) with
| ((us, t), range) -> begin
((

let uu____6852 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____6852) with
| true -> begin
(

let uu____6853 = (

let uu____6854 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____6854))
in (

let uu____6855 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____6856 = (FStar_Range.string_of_range range)
in (

let uu____6857 = (FStar_Range.string_of_use_range range)
in (

let uu____6858 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____6853 uu____6855 uu____6856 uu____6857 uu____6858))))))
end
| uu____6859 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____6863 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6863 us))
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

let uu____6887 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6887) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____6901 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____6901) with
| (env2, uu____6915) -> begin
(

let uu____6920 = (tc_binders env2 bs1)
in (match (uu____6920) with
| (bs2, env3, g, us) -> begin
(

let uu____6939 = (tc_comp env3 c1)
in (match (uu____6939) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___80_6958 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___80_6958.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___80_6958.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____6967 = (FStar_TypeChecker_Rel.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Rel.conj_guard g uu____6967))
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

let uu____6983 = (

let uu____6988 = (

let uu____6989 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6989)::[])
in (FStar_Syntax_Subst.open_term uu____6988 phi))
in (match (uu____6983) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____7011 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____7011) with
| (env2, uu____7025) -> begin
(

let uu____7030 = (

let uu____7043 = (FStar_List.hd x1)
in (tc_binder env2 uu____7043))
in (match (uu____7030) with
| (x2, env3, f1, u) -> begin
((

let uu____7071 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____7071) with
| true -> begin
(

let uu____7072 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____7073 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____7074 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____7072 uu____7073 uu____7074))))
end
| uu____7075 -> begin
()
end));
(

let uu____7076 = (FStar_Syntax_Util.type_u ())
in (match (uu____7076) with
| (t_phi, uu____7088) -> begin
(

let uu____7089 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____7089) with
| (phi2, uu____7103, f2) -> begin
(

let e1 = (

let uu___81_7108 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___81_7108.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___81_7108.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____7115 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____7115))
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____7135) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____7158 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____7158) with
| true -> begin
(

let uu____7159 = (FStar_Syntax_Print.term_to_string (

let uu___82_7162 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.pos = uu___82_7162.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___82_7162.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____7159))
end
| uu____7173 -> begin
()
end));
(

let uu____7174 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____7174) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____7187 -> begin
(

let uu____7188 = (

let uu____7189 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____7190 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____7189 uu____7190)))
in (failwith uu____7188))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Syntax_Syntax.t_unit
end
| FStar_Const.Const_bool (uu____7200) -> begin
FStar_Syntax_Util.t_bool
end
| FStar_Const.Const_int (uu____7201, FStar_Pervasives_Native.None) -> begin
FStar_Syntax_Syntax.t_int
end
| FStar_Const.Const_int (uu____7212, FStar_Pervasives_Native.Some (msize)) -> begin
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
| FStar_Const.Const_string (uu____7228) -> begin
FStar_Syntax_Syntax.t_string
end
| FStar_Const.Const_float (uu____7233) -> begin
FStar_Syntax_Syntax.t_float
end
| FStar_Const.Const_char (uu____7234) -> begin
(

let uu____7235 = (

let uu____7240 = (FStar_Syntax_DsEnv.try_lookup_lid env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid)
in (FStar_All.pipe_right uu____7240 FStar_Util.must))
in (FStar_All.pipe_right uu____7235 FStar_Pervasives_Native.fst))
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____7265) -> begin
FStar_Syntax_Syntax.t_range
end
| FStar_Const.Const_range_of -> begin
(

let uu____7266 = (

let uu____7271 = (

let uu____7272 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7272))
in ((FStar_Errors.Fatal_IllTyped), (uu____7271)))
in (FStar_Errors.raise_error uu____7266 r))
end
| FStar_Const.Const_set_range_of -> begin
(

let uu____7273 = (

let uu____7278 = (

let uu____7279 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7279))
in ((FStar_Errors.Fatal_IllTyped), (uu____7278)))
in (FStar_Errors.raise_error uu____7273 r))
end
| FStar_Const.Const_reify -> begin
(

let uu____7280 = (

let uu____7285 = (

let uu____7286 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7286))
in ((FStar_Errors.Fatal_IllTyped), (uu____7285)))
in (FStar_Errors.raise_error uu____7280 r))
end
| FStar_Const.Const_reflect (uu____7287) -> begin
(

let uu____7288 = (

let uu____7293 = (

let uu____7294 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7294))
in ((FStar_Errors.Fatal_IllTyped), (uu____7293)))
in (FStar_Errors.raise_error uu____7288 r))
end
| uu____7295 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedConstant), ("Unsupported constant")) r)
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____7312) -> begin
(

let uu____7321 = (FStar_Syntax_Util.type_u ())
in (match (uu____7321) with
| (k, u) -> begin
(

let uu____7334 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____7334) with
| (t1, uu____7348, g) -> begin
(

let uu____7350 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____7350), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____7352) -> begin
(

let uu____7361 = (FStar_Syntax_Util.type_u ())
in (match (uu____7361) with
| (k, u) -> begin
(

let uu____7374 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____7374) with
| (t1, uu____7388, g) -> begin
(

let uu____7390 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____7390), (u), (g)))
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

let uu____7400 = (

let uu____7405 = (

let uu____7406 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____7406)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____7405))
in (uu____7400 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____7421 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____7421) with
| (tc1, uu____7435, f) -> begin
(

let uu____7437 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____7437) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____7481 = (

let uu____7482 = (FStar_Syntax_Subst.compress head3)
in uu____7482.FStar_Syntax_Syntax.n)
in (match (uu____7481) with
| FStar_Syntax_Syntax.Tm_uinst (uu____7485, us) -> begin
us
end
| uu____7491 -> begin
[]
end))
in (

let uu____7492 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____7492) with
| (uu____7513, args1) -> begin
(

let uu____7535 = (

let uu____7552 = (FStar_List.hd args1)
in (

let uu____7563 = (FStar_List.tl args1)
in ((uu____7552), (uu____7563))))
in (match (uu____7535) with
| (res, args2) -> begin
(

let uu____7622 = (

let uu____7631 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___68_7659 -> (match (uu___68_7659) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____7667 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____7667) with
| (env1, uu____7679) -> begin
(

let uu____7684 = (tc_tot_or_gtot_term env1 e)
in (match (uu____7684) with
| (e1, uu____7696, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____7631 FStar_List.unzip))
in (match (uu____7622) with
| (flags1, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___83_7733 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___83_7733.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___83_7733.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____7737 = (FStar_TypeChecker_Env.effect_repr env c2 u)
in (match (uu____7737) with
| FStar_Pervasives_Native.None -> begin
u
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____7741 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c2), (u_c), (uu____7741))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____7751) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____7752) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____7762 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____7762))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____7766 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____7766))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(

let uu____7770 = (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x))
in (match (uu____7770) with
| true -> begin
u2
end
| uu____7771 -> begin
(

let uu____7772 = (

let uu____7773 = (

let uu____7774 = (FStar_Syntax_Print.univ_to_string u2)
in (Prims.strcat uu____7774 " not found"))
in (Prims.strcat "Universe variable " uu____7773))
in (failwith uu____7772))
end))
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____7775 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____7776 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7776 FStar_Pervasives_Native.snd))
end
| uu____7785 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail1 = (fun msg t -> (

let uu____7814 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in (FStar_Errors.raise_error uu____7814 top.FStar_Syntax_Syntax.pos)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____7938 bs2 bs_expected1 -> (match (uu____7938) with
| (env2, out, g, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.None), (g), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((match (((imp), (imp'))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8208))) -> begin
(

let uu____8213 = (

let uu____8218 = (

let uu____8219 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____8219))
in ((FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation), (uu____8218)))
in (

let uu____8220 = (FStar_Syntax_Syntax.range_of_bv hd1)
in (FStar_Errors.raise_error uu____8213 uu____8220)))
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8221)), FStar_Pervasives_Native.None) -> begin
(

let uu____8226 = (

let uu____8231 = (

let uu____8232 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____8232))
in ((FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation), (uu____8231)))
in (

let uu____8233 = (FStar_Syntax_Syntax.range_of_bv hd1)
in (FStar_Errors.raise_error uu____8226 uu____8233)))
end
| uu____8234 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____8244 = (

let uu____8251 = (

let uu____8252 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____8252.FStar_Syntax_Syntax.n)
in (match (uu____8251) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____8261 -> begin
((

let uu____8263 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____8263) with
| true -> begin
(

let uu____8264 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____8264))
end
| uu____8265 -> begin
()
end));
(

let uu____8266 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____8266) with
| (t, uu____8280, g1) -> begin
(

let g2 = (

let uu____8283 = (FStar_TypeChecker_Rel.teq_nosmt env2 t expected_t)
in (match (uu____8283) with
| true -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____8284 -> begin
(

let uu____8285 = (FStar_TypeChecker_Rel.get_subtyping_prop env2 expected_t t)
in (match (uu____8285) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8288 = (FStar_TypeChecker_Err.basic_type_error env2 FStar_Pervasives_Native.None expected_t t)
in (

let uu____8293 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____8288 uu____8293)))
end
| FStar_Pervasives_Native.Some (g2) -> begin
(

let uu____8295 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_TypeChecker_Util.label_guard uu____8295 "Type annotation on parameter incompatible with the expected type" g2))
end))
end))
in (

let g3 = (

let uu____8297 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____8297))
in ((t), (g3))))
end));
)
end))
in (match (uu____8244) with
| (t, g1) -> begin
(

let hd2 = (

let uu___84_8345 = hd1
in {FStar_Syntax_Syntax.ppname = uu___84_8345.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___84_8345.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env3 = (push_binding env2 b)
in (

let subst2 = (

let uu____8364 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____8364))
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
| uu____8652 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____8661 = (tc_binders env1 bs)
in (match (uu____8661) with
| (bs1, envbody, g, uu____8691) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody), (body1), (g))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____8733 = (

let uu____8734 = (FStar_Syntax_Subst.compress t2)
in uu____8734.FStar_Syntax_Syntax.n)
in (match (uu____8733) with
| FStar_Syntax_Syntax.Tm_uvar (uu____8757) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____8765 -> begin
(failwith "Impossible")
end);
(

let uu____8774 = (tc_binders env1 bs)
in (match (uu____8774) with
| (bs1, envbody, g, uu____8806) -> begin
(

let uu____8807 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____8807) with
| (envbody1, uu____8835) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____8846); FStar_Syntax_Syntax.pos = uu____8847; FStar_Syntax_Syntax.vars = uu____8848}, uu____8849) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____8877 -> begin
(failwith "Impossible")
end);
(

let uu____8886 = (tc_binders env1 bs)
in (match (uu____8886) with
| (bs1, envbody, g, uu____8918) -> begin
(

let uu____8919 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____8919) with
| (envbody1, uu____8947) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____8959) -> begin
(

let uu____8964 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____8964) with
| (uu____9005, bs1, bs', copt, env2, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), (bs'), (copt), (env2), (body2), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____9048 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____9048) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 body2 -> (

let rec handle_more = (fun uu____9177 c_expected2 body3 -> (match (uu____9177) with
| (env3, bs2, more, guard, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9281 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env3), (bs2), (guard), (uu____9281), (body3)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____9296 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____9296))
in (

let uu____9297 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env3), (bs2), (guard), (uu____9297), (body3))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (

let uu____9312 = ((FStar_Options.ml_ish ()) || (FStar_Syntax_Util.is_named_tot c))
in (match (uu____9312) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env3 (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____9368 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____9368) with
| (bs_expected4, c_expected4) -> begin
(

let uu____9393 = (check_binders env3 more_bs bs_expected4)
in (match (uu____9393) with
| (env4, bs', more1, guard', subst2) -> begin
(

let uu____9445 = (

let uu____9470 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env4), ((FStar_List.append bs2 bs')), (more1), (uu____9470), (subst2)))
in (handle_more uu____9445 c_expected4 body3))
end))
end))
end
| uu____9489 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env3), (bs2), (guard), (c), (body4)))
end))
end
| uu____9501 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env3), (bs2), (guard), (c), (body4)))
end)))
end)
end))
in (

let uu____9513 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____9513 c_expected1 body2))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___85_9570 = envbody
in {FStar_TypeChecker_Env.solver = uu___85_9570.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___85_9570.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___85_9570.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___85_9570.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___85_9570.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___85_9570.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___85_9570.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___85_9570.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___85_9570.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___85_9570.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___85_9570.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___85_9570.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___85_9570.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___85_9570.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___85_9570.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___85_9570.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___85_9570.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___85_9570.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___85_9570.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___85_9570.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___85_9570.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___85_9570.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___85_9570.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___85_9570.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___85_9570.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___85_9570.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___85_9570.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___85_9570.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___85_9570.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___85_9570.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___85_9570.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___85_9570.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___85_9570.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___85_9570.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___85_9570.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___85_9570.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___85_9570.FStar_TypeChecker_Env.dep_graph})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____9628 uu____9629 -> (match (((uu____9628), (uu____9629))) with
| ((env2, letrec_binders), (l, t3, u_names)) -> begin
(

let uu____9711 = (

let uu____9718 = (

let uu____9719 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____9719 FStar_Pervasives_Native.fst))
in (tc_term uu____9718 t3))
in (match (uu____9711) with
| (t4, uu____9741, uu____9742) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l ((u_names), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____9754 = (FStar_Syntax_Syntax.mk_binder (

let uu___86_9757 = x
in {FStar_Syntax_Syntax.ppname = uu___86_9757.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___86_9757.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____9754)::letrec_binders)
end
| uu____9758 -> begin
letrec_binders
end)
in ((env3), (lb))))
end))
end)) ((envbody1), ([])))))))
in (

let uu____9767 = (check_actuals_against_formals env1 bs bs_expected1 body1)
in (match (uu____9767) with
| (envbody, bs1, g, c, body2) -> begin
(

let uu____9827 = (mk_letrec_env envbody bs1 c)
in (match (uu____9827) with
| (envbody1, letrecs) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in ((FStar_Pervasives_Native.Some (t2)), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (envbody2), (body2), (g)))
end))
end))))
end))
end
| uu____9867 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____9888 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____9888))
end
| uu____9889 -> begin
(

let uu____9890 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____9890) with
| (uu____9929, bs1, uu____9931, c_opt, envbody, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (c_opt), (envbody), (body2), (g))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____9951 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9951) with
| (env1, topt) -> begin
((

let uu____9971 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____9971) with
| true -> begin
(

let uu____9972 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____9972 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____9974 -> begin
"false"
end)))
end
| uu____9975 -> begin
()
end));
(

let uu____9976 = (expected_function_typ1 env1 topt body)
in (match (uu____9976) with
| (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1, g) -> begin
(

let uu____10016 = (

let should_check_expected_effect = (

let uu____10024 = (

let uu____10031 = (

let uu____10032 = (FStar_Syntax_Subst.compress body1)
in uu____10032.FStar_Syntax_Syntax.n)
in ((c_opt), (uu____10031)))
in (match (uu____10024) with
| (FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Tm_ascribed (uu____10037, (FStar_Util.Inr (expected_c), uu____10039), uu____10040)) -> begin
false
end
| uu____10089 -> begin
true
end))
in (

let uu____10096 = (tc_term (

let uu___87_10105 = envbody
in {FStar_TypeChecker_Env.solver = uu___87_10105.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___87_10105.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___87_10105.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___87_10105.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___87_10105.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___87_10105.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___87_10105.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___87_10105.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___87_10105.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___87_10105.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___87_10105.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___87_10105.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___87_10105.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___87_10105.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___87_10105.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___87_10105.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___87_10105.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___87_10105.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___87_10105.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___87_10105.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___87_10105.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___87_10105.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___87_10105.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___87_10105.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___87_10105.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___87_10105.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___87_10105.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___87_10105.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___87_10105.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___87_10105.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___87_10105.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___87_10105.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___87_10105.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___87_10105.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___87_10105.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___87_10105.FStar_TypeChecker_Env.dep_graph}) body1)
in (match (uu____10096) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (match (should_check_expected_effect) with
| true -> begin
(

let uu____10122 = (

let uu____10129 = (

let uu____10134 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____10134)))
in (check_expected_effect (

let uu___88_10137 = envbody
in {FStar_TypeChecker_Env.solver = uu___88_10137.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___88_10137.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___88_10137.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___88_10137.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___88_10137.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___88_10137.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___88_10137.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___88_10137.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___88_10137.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___88_10137.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___88_10137.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___88_10137.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___88_10137.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___88_10137.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___88_10137.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___88_10137.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___88_10137.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___88_10137.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___88_10137.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___88_10137.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___88_10137.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___88_10137.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___88_10137.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___88_10137.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___88_10137.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___88_10137.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___88_10137.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___88_10137.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___88_10137.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___88_10137.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___88_10137.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___88_10137.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___88_10137.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___88_10137.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___88_10137.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___88_10137.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___88_10137.FStar_TypeChecker_Env.dep_graph}) c_opt uu____10129))
in (match (uu____10122) with
| (body3, cbody1, guard) -> begin
(

let uu____10147 = (FStar_TypeChecker_Rel.conj_guard guard_body1 guard)
in ((body3), (cbody1), (uu____10147)))
end))
end
| uu____10148 -> begin
(

let uu____10149 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____10149), (guard_body1)))
end))
end)))
in (match (uu____10016) with
| (body2, cbody, guard) -> begin
(

let guard1 = (

let uu____10160 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____10162 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____10162))))
in (match (uu____10160) with
| true -> begin
(

let uu____10163 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____10163))
end
| uu____10164 -> begin
(

let guard1 = (

let uu____10166 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard env1 (FStar_List.append bs1 letrec_binders) uu____10166))
in guard1)
end))
in (

let guard2 = (FStar_TypeChecker_Util.close_guard_implicits env1 bs1 guard1)
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody)
in (

let e = (FStar_Syntax_Util.abs bs1 body2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody c_opt)))))
in (

let uu____10178 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____10199) -> begin
((e), (t1), (guard2))
end
| uu____10214 -> begin
(

let uu____10215 = (FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
in (match (uu____10215) with
| (e1, guard') -> begin
(

let uu____10228 = (FStar_TypeChecker_Rel.conj_guard guard2 guard')
in ((e1), (t1), (uu____10228)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard2))
end)
in (match (uu____10178) with
| (e1, tfun, guard3) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Total tfun)
in (

let uu____10243 = (

let uu____10248 = (FStar_Syntax_Util.lcomp_of_comp c)
in (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 uu____10248 guard3))
in (match (uu____10243) with
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

let uu____10294 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____10294) with
| true -> begin
(

let uu____10295 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____10296 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____10295 uu____10296)))
end
| uu____10297 -> begin
()
end));
(

let monadic_application = (fun uu____10367 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____10367) with
| (head2, chead1, ghead1, cres) -> begin
(

let uu____10424 = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____10424) with
| (rt, g0) -> begin
(

let cres1 = (

let uu___89_10438 = cres
in {FStar_Syntax_Syntax.eff_name = uu___89_10438.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___89_10438.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___89_10438.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____10439 = (match (bs) with
| [] -> begin
(

let g = (

let uu____10453 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.conj_guard g0) uu____10453))
in ((cres1), (g)))
end
| uu____10454 -> begin
(

let g = (

let uu____10462 = (

let uu____10463 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____10463 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (FStar_TypeChecker_Rel.conj_guard g0 uu____10462))
in (

let uu____10464 = (

let uu____10465 = (

let uu____10466 = (

let uu____10467 = (FStar_Syntax_Syntax.lcomp_comp cres1)
in (FStar_Syntax_Util.arrow bs uu____10467))
in (FStar_Syntax_Syntax.mk_Total uu____10466))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____10465))
in ((uu____10464), (g))))
end)
in (match (uu____10439) with
| (cres2, guard1) -> begin
((

let uu____10479 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____10479) with
| true -> begin
(

let uu____10480 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____10480))
end
| uu____10481 -> begin
()
end));
(

let cres3 = (

let head_is_pure_and_some_arg_is_effectful = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1) && (FStar_Util.for_some (fun uu____10496 -> (match (uu____10496) with
| (uu____10505, uu____10506, lc) -> begin
((

let uu____10514 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____10514))) || (FStar_TypeChecker_Util.should_not_inline_lc lc))
end)) arg_comps_rev))
in (

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (

let uu____10524 = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2) && head_is_pure_and_some_arg_is_effectful)
in (match (uu____10524) with
| true -> begin
((

let uu____10526 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10526) with
| true -> begin
(

let uu____10527 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: Return inserted in monadic application: %s\n" uu____10527))
end
| uu____10528 -> begin
()
end));
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2);
)
end
| uu____10529 -> begin
((

let uu____10531 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10531) with
| true -> begin
(

let uu____10532 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: No return inserted in monadic application: %s\n" uu____10532))
end
| uu____10533 -> begin
()
end));
cres2;
)
end))))
in (

let comp = (FStar_List.fold_left (fun out_c uu____10556 -> (match (uu____10556) with
| ((e, q), x, c) -> begin
((

let uu____10582 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10582) with
| true -> begin
(

let uu____10583 = (match (x) with
| FStar_Pervasives_Native.None -> begin
"_"
end
| FStar_Pervasives_Native.Some (x1) -> begin
(FStar_Syntax_Print.bv_to_string x1)
end)
in (

let uu____10585 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print2 "(b) Monadic app: Binding argument %s : %s\n" uu____10583 uu____10585)))
end
| uu____10586 -> begin
()
end));
(

let uu____10587 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____10587) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____10590 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end));
)
end)) cres3 arg_comps_rev)
in (

let comp1 = ((

let uu____10595 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10595) with
| true -> begin
(

let uu____10596 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print1 "(c) Monadic app: Binding head %s " uu____10596))
end
| uu____10597 -> begin
()
end));
(

let uu____10598 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1)
in (match (uu____10598) with
| true -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (head2)) chead1 ((FStar_Pervasives_Native.None), (comp)))
end
| uu____10601 -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
end));
)
in (

let comp2 = (FStar_TypeChecker_Util.subst_lcomp subst1 comp1)
in (

let shortcuts_evaluation_order = (

let uu____10606 = (

let uu____10607 = (FStar_Syntax_Subst.compress head2)
in uu____10607.FStar_Syntax_Syntax.n)
in (match (uu____10606) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____10611 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____10636 -> (match (uu____10636) with
| (arg, uu____10650, uu____10651) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ))))
end
| uu____10660 -> begin
(

let uu____10661 = (

let map_fun = (fun uu____10727 -> (match (uu____10727) with
| ((e, q), uu____10762, c) -> begin
(

let uu____10772 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____10772) with
| true -> begin
((FStar_Pervasives_Native.None), (((e), (q))))
end
| uu____10819 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____10822 = (

let uu____10827 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____10827), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____10822)))))
end))
end))
in (

let uu____10856 = (

let uu____10883 = (

let uu____10906 = (

let uu____10917 = (

let uu____10926 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____10926), (FStar_Pervasives_Native.None), (chead1)))
in (uu____10917)::arg_comps_rev)
in (FStar_List.map map_fun uu____10906))
in (FStar_All.pipe_left FStar_List.split uu____10883))
in (match (uu____10856) with
| (lifted_args, reverse_args) -> begin
(

let uu____11103 = (

let uu____11104 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____11104))
in (

let uu____11113 = (

let uu____11120 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____11120))
in ((lifted_args), (uu____11103), (uu____11113))))
end)))
in (match (uu____10661) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___69_11239 -> (match (uu___69_11239) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1 [] e1.FStar_Syntax_Syntax.pos)
in (

let letbinding = (

let uu____11300 = (

let uu____11307 = (

let uu____11308 = (

let uu____11321 = (

let uu____11324 = (

let uu____11325 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____11325)::[])
in (FStar_Syntax_Subst.close uu____11324 e))
in ((((false), ((lb)::[]))), (uu____11321)))
in FStar_Syntax_Syntax.Tm_let (uu____11308))
in (FStar_Syntax_Syntax.mk uu____11307))
in (uu____11300 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp2.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____11371 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp2 guard1)
in (match (uu____11371) with
| (comp3, g) -> begin
((

let uu____11388 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____11388) with
| true -> begin
(

let uu____11389 = (FStar_Syntax_Print.term_to_string app)
in (

let uu____11390 = (FStar_Syntax_Print.lcomp_to_string comp3)
in (FStar_Util.print2 "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n" uu____11389 uu____11390)))
end
| uu____11391 -> begin
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

let rec tc_args = (fun head_info uu____11468 bs args1 -> (match (uu____11468) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11607))))::rest, ((uu____11609, FStar_Pervasives_Native.None))::uu____11610) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____11670 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (match (uu____11670) with
| (t1, g_ex) -> begin
(

let uu____11683 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____11683) with
| (varg, uu____11703, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____11727 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____11727)))
in (

let uu____11728 = (

let uu____11763 = (

let uu____11778 = (

let uu____11791 = (

let uu____11792 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____11792 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____11791)))
in (uu____11778)::outargs)
in (

let uu____11811 = (

let uu____11812 = (FStar_TypeChecker_Rel.conj_guard g_ex g)
in (FStar_TypeChecker_Rel.conj_guard implicits uu____11812))
in ((subst2), (uu____11763), ((arg)::arg_rets), (uu____11811), (fvs))))
in (tc_args head_info uu____11728 rest args1))))
end))
end)))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11914)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11915))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____11928 -> begin
(

let uu____11937 = (

let uu____11942 = (

let uu____11943 = (FStar_Syntax_Print.aqual_to_string aqual)
in (

let uu____11944 = (FStar_Syntax_Print.aqual_to_string aq)
in (

let uu____11945 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____11946 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format4 "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s" uu____11943 uu____11944 uu____11945 uu____11946)))))
in ((FStar_Errors.Fatal_InconsistentImplicitQualifier), (uu____11942)))
in (FStar_Errors.raise_error uu____11937 e.FStar_Syntax_Syntax.pos))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___90_11949 = x
in {FStar_Syntax_Syntax.ppname = uu___90_11949.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___90_11949.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____11951 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____11951) with
| true -> begin
(

let uu____11952 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____11952))
end
| uu____11953 -> begin
()
end));
(

let uu____11954 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (match (uu____11954) with
| (targ1, g_ex) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___91_11969 = env1
in {FStar_TypeChecker_Env.solver = uu___91_11969.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___91_11969.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___91_11969.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___91_11969.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___91_11969.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___91_11969.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___91_11969.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___91_11969.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___91_11969.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___91_11969.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___91_11969.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___91_11969.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___91_11969.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___91_11969.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___91_11969.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___91_11969.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___91_11969.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___91_11969.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___91_11969.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___91_11969.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___91_11969.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___91_11969.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___91_11969.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___91_11969.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___91_11969.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___91_11969.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___91_11969.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___91_11969.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___91_11969.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___91_11969.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___91_11969.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___91_11969.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___91_11969.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___91_11969.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___91_11969.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___91_11969.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___91_11969.FStar_TypeChecker_Env.dep_graph})
in ((

let uu____11971 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____11971) with
| true -> begin
(

let uu____11972 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____11973 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11974 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____11972 uu____11973 uu____11974))))
end
| uu____11975 -> begin
()
end));
(

let uu____11976 = (tc_term env2 e)
in (match (uu____11976) with
| (e1, c, g_e) -> begin
(

let g1 = (

let uu____11993 = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.conj_guard g_ex) uu____11993))
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____12012 = (

let uu____12015 = (

let uu____12022 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____12022))
in (FStar_Pervasives_Native.fst uu____12015))
in ((uu____12012), (aq)))
in (

let uu____12029 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____12029) with
| true -> begin
(

let subst2 = (

let uu____12037 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____12037 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____12100 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
)))
end));
)));
)
end
| (uu____12155, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____12191) -> begin
(

let uu____12242 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____12242) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 solve ghead2 tres -> (

let tres1 = (

let uu____12290 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____12290 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____12315 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____12315) with
| (bs2, cres'1) -> begin
(

let head_info1 = (

let uu____12337 = (FStar_Syntax_Util.lcomp_of_comp cres'1)
in ((head2), (chead1), (ghead2), (uu____12337)))
in ((

let uu____12339 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____12339) with
| true -> begin
(FStar_Errors.log_issue tres1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_RedundantExplicitCurrying), ("Potentially redundant explicit currying of a function type")))
end
| uu____12340 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____12381 when (not (norm1)) -> begin
(

let rec norm_tres = (fun tres2 -> (

let tres3 = (FStar_TypeChecker_Normalize.unfold_whnf env tres2)
in (

let uu____12389 = (

let uu____12390 = (FStar_Syntax_Subst.compress tres3)
in uu____12390.FStar_Syntax_Syntax.n)
in (match (uu____12389) with
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____12393; FStar_Syntax_Syntax.index = uu____12394; FStar_Syntax_Syntax.sort = tres4}, uu____12396) -> begin
(norm_tres tres4)
end
| uu____12403 -> begin
tres3
end))))
in (

let uu____12404 = (norm_tres tres1)
in (aux true solve ghead2 uu____12404)))
end
| uu____12405 when (not (solve)) -> begin
(

let ghead3 = (FStar_TypeChecker_Rel.solve_deferred_constraints env ghead2)
in (aux norm1 solve ghead3 tres1))
end
| uu____12407 -> begin
(

let uu____12408 = (

let uu____12413 = (

let uu____12414 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____12415 = (FStar_Util.string_of_int n_args)
in (

let uu____12422 = (FStar_Syntax_Print.term_to_string tres1)
in (FStar_Util.format3 "Too many arguments to function of type %s; got %s arguments, remaining type is %s" uu____12414 uu____12415 uu____12422))))
in ((FStar_Errors.Fatal_ToManyArgumentToFunction), (uu____12413)))
in (

let uu____12423 = (FStar_Syntax_Syntax.argpos arg)
in (FStar_Errors.raise_error uu____12408 uu____12423)))
end)))
in (aux false false ghead1 chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf guard -> (

let uu____12451 = (

let uu____12452 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____12452.FStar_Syntax_Syntax.n)
in (match (uu____12451) with
| FStar_Syntax_Syntax.Tm_uvar (uu____12461) -> begin
(

let uu____12462 = (FStar_List.fold_right (fun uu____12491 uu____12492 -> (match (uu____12492) with
| (bs, guard1) -> begin
(

let uu____12517 = (

let uu____12530 = (

let uu____12531 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12531 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____12530))
in (match (uu____12517) with
| (t, uu____12547, g) -> begin
(

let uu____12561 = (

let uu____12564 = (FStar_Syntax_Syntax.null_binder t)
in (uu____12564)::bs)
in (

let uu____12565 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in ((uu____12561), (uu____12565))))
end))
end)) args (([]), (guard)))
in (match (uu____12462) with
| (bs, guard1) -> begin
(

let uu____12582 = (

let uu____12587 = (

let uu____12600 = (

let uu____12601 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12601 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____12600))
in (match (uu____12587) with
| (t, uu____12615, g) -> begin
(

let uu____12629 = (FStar_Options.ml_ish ())
in (match (uu____12629) with
| true -> begin
(

let uu____12634 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____12635 = (FStar_TypeChecker_Rel.conj_guard guard1 g)
in ((uu____12634), (uu____12635))))
end
| uu____12636 -> begin
(

let uu____12637 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____12638 = (FStar_TypeChecker_Rel.conj_guard guard1 g)
in ((uu____12637), (uu____12638))))
end))
end))
in (match (uu____12582) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____12651 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____12651) with
| true -> begin
(

let uu____12652 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____12653 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____12654 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____12652 uu____12653 uu____12654))))
end
| uu____12655 -> begin
()
end));
(

let g = (

let uu____12657 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____12657))
in (

let uu____12658 = (FStar_TypeChecker_Rel.conj_guard g guard2)
in (check_function_app bs_cres uu____12658)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12659); FStar_Syntax_Syntax.pos = uu____12660; FStar_Syntax_Syntax.vars = uu____12661}, uu____12662) -> begin
(

let uu____12683 = (FStar_List.fold_right (fun uu____12712 uu____12713 -> (match (uu____12713) with
| (bs, guard1) -> begin
(

let uu____12738 = (

let uu____12751 = (

let uu____12752 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12752 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____12751))
in (match (uu____12738) with
| (t, uu____12768, g) -> begin
(

let uu____12782 = (

let uu____12785 = (FStar_Syntax_Syntax.null_binder t)
in (uu____12785)::bs)
in (

let uu____12786 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in ((uu____12782), (uu____12786))))
end))
end)) args (([]), (guard)))
in (match (uu____12683) with
| (bs, guard1) -> begin
(

let uu____12803 = (

let uu____12808 = (

let uu____12821 = (

let uu____12822 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12822 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____12821))
in (match (uu____12808) with
| (t, uu____12836, g) -> begin
(

let uu____12850 = (FStar_Options.ml_ish ())
in (match (uu____12850) with
| true -> begin
(

let uu____12855 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____12856 = (FStar_TypeChecker_Rel.conj_guard guard1 g)
in ((uu____12855), (uu____12856))))
end
| uu____12857 -> begin
(

let uu____12858 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____12859 = (FStar_TypeChecker_Rel.conj_guard guard1 g)
in ((uu____12858), (uu____12859))))
end))
end))
in (match (uu____12803) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____12872 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____12872) with
| true -> begin
(

let uu____12873 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____12874 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____12875 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____12873 uu____12874 uu____12875))))
end
| uu____12876 -> begin
()
end));
(

let g = (

let uu____12878 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____12878))
in (

let uu____12879 = (FStar_TypeChecker_Rel.conj_guard g guard2)
in (check_function_app bs_cres uu____12879)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____12898 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____12898) with
| (bs1, c1) -> begin
(

let head_info = (

let uu____12920 = (FStar_Syntax_Util.lcomp_of_comp c1)
in ((head1), (chead), (ghead), (uu____12920)))
in (tc_args head_info (([]), ([]), ([]), (guard), ([])) bs1 args))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____12962) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort guard)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____12968, uu____12969) -> begin
(check_function_app t guard)
end
| uu____13010 -> begin
(

let uu____13011 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in (FStar_Errors.raise_error uu____13011 head1.FStar_Syntax_Syntax.pos))
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

let uu____13083 = (FStar_List.fold_left2 (fun uu____13128 uu____13129 uu____13130 -> (match (((uu____13128), (uu____13129), (uu____13130))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((Prims.op_disEquality aq aq')) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InconsistentImplicitQualifier), ("Inconsistent implicit qualifiers")) e.FStar_Syntax_Syntax.pos)
end
| uu____13199 -> begin
()
end);
(

let uu____13200 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____13200) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____13220 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____13220 g))
in (

let ghost1 = (ghost || ((

let uu____13224 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____13224))) && (

let uu____13226 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____13226)))))
in (

let uu____13227 = (

let uu____13230 = (

let uu____13233 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____13233)::[])
in (FStar_List.append seen uu____13230))
in (

let uu____13234 = (FStar_TypeChecker_Rel.conj_guard guard g1)
in ((uu____13227), (uu____13234), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____13083) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____13256 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____13256 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____13257 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____13258 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____13258) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____13274 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp) * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____13317 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____13317) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____13362 = branch1
in (match (uu____13362) with
| (cpat, uu____13403, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let tc_annot = (fun env1 t -> (

let uu____13480 = (FStar_Syntax_Util.type_u ())
in (match (uu____13480) with
| (tu, u) -> begin
(

let uu____13491 = (tc_check_tot_or_gtot_term env1 t tu)
in (match (uu____13491) with
| (t1, uu____13503, g) -> begin
((t1), (g))
end))
end)))
in (

let uu____13505 = (FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 tc_annot)
in (match (uu____13505) with
| (pat_bvs1, exp, guard_pat_annots, p) -> begin
((

let uu____13539 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13539) with
| true -> begin
(

let uu____13540 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____13541 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____13540 uu____13541)))
end
| uu____13542 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs1)
in (

let uu____13544 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____13544) with
| (env1, uu____13566) -> begin
(

let env11 = (

let uu___92_13572 = env1
in {FStar_TypeChecker_Env.solver = uu___92_13572.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___92_13572.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___92_13572.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___92_13572.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___92_13572.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___92_13572.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___92_13572.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___92_13572.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___92_13572.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___92_13572.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___92_13572.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___92_13572.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___92_13572.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___92_13572.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___92_13572.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___92_13572.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___92_13572.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___92_13572.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___92_13572.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___92_13572.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___92_13572.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___92_13572.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___92_13572.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___92_13572.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___92_13572.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___92_13572.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___92_13572.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___92_13572.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___92_13572.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___92_13572.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___92_13572.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___92_13572.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___92_13572.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___92_13572.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___92_13572.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___92_13572.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___92_13572.FStar_TypeChecker_Env.dep_graph})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in ((

let uu____13575 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13575) with
| true -> begin
(

let uu____13576 = (FStar_Syntax_Print.term_to_string exp)
in (

let uu____13577 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____13576 uu____13577)))
end
| uu____13578 -> begin
()
end));
(

let env12 = (FStar_TypeChecker_Env.set_expected_typ env11 expected_pat_t)
in (

let uu____13580 = (tc_tot_or_gtot_term env12 exp)
in (match (uu____13580) with
| (exp1, lc, g) -> begin
(

let g1 = (

let uu___93_13605 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___93_13605.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___93_13605.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___93_13605.FStar_TypeChecker_Env.implicits})
in (

let uu____13606 = (

let uu____13607 = (FStar_TypeChecker_Rel.teq_nosmt env12 lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (match (uu____13607) with
| true -> begin
(

let env13 = (FStar_TypeChecker_Env.set_range env12 exp1.FStar_Syntax_Syntax.pos)
in (

let uu____13609 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env13 g1)
in (FStar_All.pipe_right uu____13609 (FStar_TypeChecker_Rel.resolve_implicits env13))))
end
| uu____13610 -> begin
(

let uu____13611 = (

let uu____13616 = (

let uu____13617 = (FStar_Syntax_Print.term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____13618 = (FStar_Syntax_Print.term_to_string expected_pat_t)
in (FStar_Util.format2 "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)" uu____13617 uu____13618)))
in ((FStar_Errors.Fatal_MismatchedPatternType), (uu____13616)))
in (FStar_Errors.raise_error uu____13611 exp1.FStar_Syntax_Syntax.pos))
end))
in (

let norm_exp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env12 exp1)
in (

let uvs_to_string = (fun uvs -> (

let uu____13630 = (

let uu____13633 = (FStar_Util.set_elements uvs)
in (FStar_All.pipe_right uu____13633 (FStar_List.map (fun u -> (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)))))
in (FStar_All.pipe_right uu____13630 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars norm_exp)
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____13651 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Free")))
in (match (uu____13651) with
| true -> begin
((

let uu____13653 = (FStar_Syntax_Print.term_to_string norm_exp)
in (

let uu____13654 = (uvs_to_string uvs1)
in (FStar_Util.print2 ">> free_1(%s) = %s\n" uu____13653 uu____13654)));
(

let uu____13655 = (FStar_Syntax_Print.term_to_string expected_pat_t)
in (

let uu____13656 = (uvs_to_string uvs2)
in (FStar_Util.print2 ">> free_2(%s) = %s\n" uu____13655 uu____13656)));
)
end
| uu____13657 -> begin
()
end));
(

let uu____13659 = (

let uu____13660 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____13660))
in (match (uu____13659) with
| true -> begin
(

let unresolved = (FStar_Util.set_difference uvs1 uvs2)
in (

let uu____13664 = (

let uu____13669 = (

let uu____13670 = (FStar_TypeChecker_Normalize.term_to_string env norm_exp)
in (

let uu____13671 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____13672 = (uvs_to_string unresolved)
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____13670 uu____13671 uu____13672))))
in ((FStar_Errors.Fatal_UnresolvedPatternVar), (uu____13669)))
in (FStar_Errors.raise_error uu____13664 p.FStar_Syntax_Syntax.p)))
end
| uu____13673 -> begin
()
end));
(

let uu____13675 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13675) with
| true -> begin
(

let uu____13676 = (FStar_TypeChecker_Normalize.term_to_string env exp1)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____13676))
end
| uu____13677 -> begin
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

let uu____13685 = (

let uu____13692 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____13692 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____13685) with
| (scrutinee_env, uu____13725) -> begin
(

let uu____13730 = (tc_pat true pat_t pattern)
in (match (uu____13730) with
| (pattern1, pat_bvs1, pat_env, pat_exp, guard_pat_annots, norm_pat_exp) -> begin
(

let uu____13780 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____13802 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____13802) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_WhenClauseNotSupported), ("When clauses are not yet supported in --verify mode; they will be some day")) e.FStar_Syntax_Syntax.pos)
end
| uu____13815 -> begin
(

let uu____13816 = (

let uu____13823 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_Syntax_Util.t_bool)
in (tc_term uu____13823 e))
in (match (uu____13816) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____13780) with
| (when_clause1, g_when) -> begin
(

let uu____13866 = (tc_term pat_env branch_exp)
in (match (uu____13866) with
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

let uu____13908 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) uu____13908))
end)
in (

let uu____13911 = (

let eqs = (

let uu____13930 = (

let uu____13931 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____13931)))
in (match (uu____13930) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13934 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____13938) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____13939) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____13940) -> begin
FStar_Pervasives_Native.None
end
| uu____13941 -> begin
(

let uu____13942 = (

let uu____13943 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____13943 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____13942))
end))
end))
in (

let uu____13944 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch1)
in (match (uu____13944) with
| (c1, g_branch2) -> begin
(

let uu____13969 = (match (((eqs), (when_condition))) with
| uu____13982 when (

let uu____13991 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____13991))) -> begin
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

let uu____14003 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____14004 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____14003), (uu____14004))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____14013 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____14013))
in (

let uu____14014 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____14015 = (

let uu____14016 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____14016 g_when))
in ((uu____14014), (uu____14015))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____14024 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____14024), (g_when)))))
end)
in (match (uu____13969) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let maybe_return_c_weak = (fun should_return -> (

let c_weak1 = (

let uu____14060 = (should_return && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c_weak))
in (match (uu____14060) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env branch_exp1 c_weak)
end
| uu____14061 -> begin
c_weak
end))
in (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak1)))
in (

let uu____14062 = (FStar_TypeChecker_Rel.close_guard env binders g_when_weak)
in ((c_weak.FStar_Syntax_Syntax.eff_name), (c_weak.FStar_Syntax_Syntax.cflags), (maybe_return_c_weak), (uu____14062), (g_branch2)))))
end))
end)))
in (match (uu____13911) with
| (effect_label, cflags, maybe_return_c, g_when1, g_branch2) -> begin
(

let branch_guard = (

let uu____14109 = (

let uu____14110 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____14110)))
in (match (uu____14109) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____14111 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____14148 = (

let uu____14149 = (

let uu____14150 = (

let uu____14153 = (

let uu____14160 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____14160))
in (FStar_Pervasives_Native.snd uu____14153))
in (FStar_List.length uu____14150))
in (uu____14149 > (Prims.parse_int "1")))
in (match (uu____14148) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____14166 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____14166) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____14187 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____14202 = (

let uu____14207 = (

let uu____14208 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____14208)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____14207))
in (uu____14202 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____14229 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____14229)::[])))
end)))
end
| uu____14230 -> begin
[]
end)))
in (

let fail1 = (fun uu____14236 -> (

let uu____14237 = (

let uu____14238 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____14239 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____14240 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____14238 uu____14239 uu____14240))))
in (failwith uu____14237)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____14253) -> begin
(head_constructor t1)
end
| uu____14258 -> begin
(fail1 ())
end))
in (

let pat_exp2 = (

let uu____14262 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____14262 FStar_Syntax_Util.unmeta))
in (match (pat_exp2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____14267) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____14268); FStar_Syntax_Syntax.pos = uu____14269; FStar_Syntax_Syntax.vars = uu____14270}, uu____14271) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_name (uu____14292) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (c1) -> begin
(

let uu____14294 = (

let uu____14295 = (tc_constant env pat_exp2.FStar_Syntax_Syntax.pos c1)
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____14295 scrutinee_tm1 pat_exp2))
in (uu____14294)::[])
end
| FStar_Syntax_Syntax.Tm_uinst (uu____14296) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____14304 = (

let uu____14305 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____14305)))
in (match (uu____14304) with
| true -> begin
[]
end
| uu____14308 -> begin
(

let uu____14309 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____14309))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____14312) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____14314 = (

let uu____14315 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____14315)))
in (match (uu____14314) with
| true -> begin
[]
end
| uu____14318 -> begin
(

let uu____14319 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____14319))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let f = (head_constructor head1)
in (

let uu____14345 = (

let uu____14346 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____14346)))
in (match (uu____14345) with
| true -> begin
[]
end
| uu____14349 -> begin
(

let sub_term_guards = (

let uu____14353 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____14385 -> (match (uu____14385) with
| (ei, uu____14395) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____14401 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____14401) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____14422 -> begin
(

let sub_term = (

let uu____14436 = (

let uu____14441 = (

let uu____14442 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar uu____14442 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None))
in (

let uu____14443 = (

let uu____14444 = (FStar_Syntax_Syntax.as_arg scrutinee_tm1)
in (uu____14444)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____14441 uu____14443)))
in (uu____14436 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____14353 FStar_List.flatten))
in (

let uu____14471 = (discriminate scrutinee_tm1 f)
in (FStar_List.append uu____14471 sub_term_guards)))
end)))
end
| uu____14474 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pat -> (

let uu____14490 = (

let uu____14491 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____14491)))
in (match (uu____14490) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____14492 -> begin
(

let t = (

let uu____14494 = (build_branch_guard scrutinee_tm1 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____14494))
in (

let uu____14499 = (FStar_Syntax_Util.type_u ())
in (match (uu____14499) with
| (k, uu____14505) -> begin
(

let uu____14506 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____14506) with
| (t1, uu____14514, uu____14515) -> begin
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

let uu____14521 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____14521) with
| true -> begin
(

let uu____14522 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____14522))
end
| uu____14523 -> begin
()
end));
(

let uu____14524 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in (

let uu____14541 = (

let uu____14542 = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (FStar_TypeChecker_Util.close_guard_implicits env uu____14542 guard))
in ((uu____14524), (branch_guard), (effect_label), (cflags), (maybe_return_c), (uu____14541))));
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

let uu____14583 = (check_let_bound_def true env1 lb)
in (match (uu____14583) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____14605 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____14622 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____14622), (univ_vars1), (c1)))
end
| uu____14623 -> begin
(

let g11 = (

let uu____14625 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____14625 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let uu____14627 = (

let uu____14640 = (

let uu____14655 = (

let uu____14664 = (

let uu____14671 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____14671)))
in (uu____14664)::[])
in (FStar_TypeChecker_Util.generalize env1 false uu____14655))
in (FStar_List.hd uu____14640))
in (match (uu____14627) with
| (uu____14708, univs1, e11, c11, gvs) -> begin
(

let g12 = (FStar_All.pipe_left (FStar_TypeChecker_Rel.map_guard g11) (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env1))
in (

let g13 = (FStar_TypeChecker_Rel.abstract_guard_n gvs g12)
in (

let uu____14722 = (FStar_Syntax_Util.lcomp_of_comp c11)
in ((g13), (e11), (univs1), (uu____14722)))))
end)))
end)
in (match (uu____14605) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____14733 = (

let uu____14742 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____14742) with
| true -> begin
(

let uu____14751 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____14751) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____14776 -> begin
((

let uu____14778 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____14778 FStar_TypeChecker_Err.top_level_effect));
(

let uu____14779 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____14779), (c12)));
)
end)
end))
end
| uu____14786 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____14791 = (FStar_Syntax_Syntax.lcomp_comp c11)
in (FStar_All.pipe_right uu____14791 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env1)))
in (

let e21 = (

let uu____14797 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____14797) with
| true -> begin
e2
end
| uu____14800 -> begin
((

let uu____14802 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____14802 FStar_TypeChecker_Err.top_level_effect));
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos);
)
end))
in ((e21), (c))));
)
end))
in (match (uu____14733) with
| (e21, c12) -> begin
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit)
in (

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e11 lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
in (

let uu____14829 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____14840 = (FStar_Syntax_Util.lcomp_of_comp cres)
in ((uu____14829), (uu____14840), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| uu____14841 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___94_14872 = env1
in {FStar_TypeChecker_Env.solver = uu___94_14872.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___94_14872.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___94_14872.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___94_14872.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___94_14872.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___94_14872.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___94_14872.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___94_14872.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___94_14872.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___94_14872.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___94_14872.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___94_14872.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___94_14872.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___94_14872.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___94_14872.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___94_14872.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___94_14872.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___94_14872.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___94_14872.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___94_14872.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___94_14872.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___94_14872.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___94_14872.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___94_14872.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___94_14872.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___94_14872.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___94_14872.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___94_14872.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___94_14872.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___94_14872.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___94_14872.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___94_14872.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___94_14872.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___94_14872.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___94_14872.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___94_14872.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___94_14872.FStar_TypeChecker_Env.dep_graph})
in (

let uu____14873 = (

let uu____14884 = (

let uu____14885 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____14885 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____14884 lb))
in (match (uu____14873) with
| (e1, uu____14907, c1, g1, annotated) -> begin
((

let uu____14912 = ((FStar_Util.for_some (FStar_Syntax_Util.is_fvar FStar_Parser_Const.inline_let_attr) lb.FStar_Syntax_Syntax.lbattrs) && (

let uu____14916 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c1)
in (not (uu____14916))))
in (match (uu____14912) with
| true -> begin
(

let uu____14917 = (

let uu____14922 = (

let uu____14923 = (FStar_Syntax_Print.term_to_string e1)
in (

let uu____14924 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.format2 "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\"" uu____14923 uu____14924)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____14922)))
in (FStar_Errors.raise_error uu____14917 e1.FStar_Syntax_Syntax.pos))
end
| uu____14925 -> begin
()
end));
(

let x = (

let uu___95_14927 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___95_14927.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___95_14927.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____14928 = (

let uu____14933 = (

let uu____14934 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____14934)::[])
in (FStar_Syntax_Subst.open_term uu____14933 e2))
in (match (uu____14928) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let env_x = (FStar_TypeChecker_Env.push_bv env2 x1)
in (

let uu____14966 = (tc_term env_x e21)
in (match (uu____14966) with
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

let uu____14991 = (

let uu____14998 = (

let uu____14999 = (

let uu____15012 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____15012)))
in FStar_Syntax_Syntax.Tm_let (uu____14999))
in (FStar_Syntax_Syntax.mk uu____14998))
in (uu____14991 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____15030 = (

let uu____15031 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____15032 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____15031 c1.FStar_Syntax_Syntax.res_typ uu____15032 e11)))
in (FStar_All.pipe_left (fun _0_19 -> FStar_TypeChecker_Common.NonTrivial (_0_19)) uu____15030))
in (

let g21 = (

let uu____15034 = (

let uu____15035 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____15035 g2))
in (FStar_TypeChecker_Rel.close_guard env2 xb uu____15034))
in (

let g22 = (FStar_TypeChecker_Util.close_guard_implicits env2 xb g21)
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g22)
in (

let uu____15038 = (

let uu____15039 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____15039))
in (match (uu____15038) with
| true -> begin
(

let tt = (

let uu____15049 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____15049 FStar_Option.get))
in ((

let uu____15055 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____15055) with
| true -> begin
(

let uu____15056 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____15057 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____15056 uu____15057)))
end
| uu____15058 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____15059 -> begin
(

let uu____15060 = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____15060) with
| (t, g_ex) -> begin
((

let uu____15074 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____15074) with
| true -> begin
(

let uu____15075 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____15076 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____15075 uu____15076)))
end
| uu____15077 -> begin
()
end));
(

let uu____15078 = (FStar_TypeChecker_Rel.conj_guard g_ex guard)
in ((e4), ((

let uu___96_15080 = cres
in {FStar_Syntax_Syntax.eff_name = uu___96_15080.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___96_15080.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___96_15080.FStar_Syntax_Syntax.comp_thunk})), (uu____15078)));
)
end))
end))))))))))))
end)))))
end)));
)
end)))
end
| uu____15081 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____15113 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____15113) with
| (lbs1, e21) -> begin
(

let uu____15132 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____15132) with
| (env0, topt) -> begin
(

let uu____15151 = (build_let_rec_env true env0 lbs1)
in (match (uu____15151) with
| (lbs2, rec_env) -> begin
(

let uu____15170 = (check_let_recs rec_env lbs2)
in (match (uu____15170) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____15190 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g_lbs)
in (FStar_All.pipe_right uu____15190 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let all_lb_names = (

let uu____15196 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____15196 (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((Prims.op_Equality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
lb
end
| uu____15228 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)))))
end
| uu____15229 -> begin
(

let ecs = (

let uu____15245 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____15279 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____15279))))))
in (FStar_TypeChecker_Util.generalize env1 true uu____15245))
in (FStar_List.map2 (fun uu____15311 lb -> (match (uu____15311) with
| (x, uvs, e, c, gvs) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)) ecs lbs3))
end)
in (

let cres = (

let uu____15353 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____15353))
in (

let uu____15354 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____15354) with
| (lbs5, e22) -> begin
((

let uu____15374 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____15374 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____15375 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____15375), (cres), (FStar_TypeChecker_Rel.trivial_guard)));
)
end))))))
end))
end))
end))
end))
end
| uu____15386 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____15418 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____15418) with
| (lbs1, e21) -> begin
(

let uu____15437 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____15437) with
| (env0, topt) -> begin
(

let uu____15456 = (build_let_rec_env false env0 lbs1)
in (match (uu____15456) with
| (lbs2, rec_env) -> begin
(

let uu____15475 = (check_let_recs rec_env lbs2)
in (match (uu____15475) with
| (lbs3, g_lbs) -> begin
(

let uu____15494 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___97_15517 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___97_15517.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___97_15517.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___98_15519 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___98_15519.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___98_15519.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___98_15519.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___98_15519.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___98_15519.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___98_15519.FStar_Syntax_Syntax.lbpos})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____15494) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____15546 = (tc_term env2 e21)
in (match (uu____15546) with
| (e22, cres, g2) -> begin
(

let cres1 = (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e22 cres)
in (

let cres2 = (FStar_Syntax_Util.lcomp_set_flags cres1 ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
in (

let guard = (

let uu____15565 = (

let uu____15566 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Rel.close_guard env2 uu____15566 g2))
in (FStar_TypeChecker_Rel.conj_guard g_lbs uu____15565))
in (

let cres3 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres2)
in (

let tres = (norm env2 cres3.FStar_Syntax_Syntax.res_typ)
in (

let cres4 = (

let uu___99_15574 = cres3
in {FStar_Syntax_Syntax.eff_name = uu___99_15574.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___99_15574.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___99_15574.FStar_Syntax_Syntax.comp_thunk})
in (

let guard1 = (

let bs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (

let uu____15582 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____15582)))))
in (FStar_TypeChecker_Util.close_guard_implicits env2 bs guard))
in (

let uu____15583 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____15583) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____15621) -> begin
((e), (cres4), (guard1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____15622 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (match (uu____15622) with
| (tres1, g_ex) -> begin
(

let cres5 = (

let uu___100_15636 = cres4
in {FStar_Syntax_Syntax.eff_name = uu___100_15636.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___100_15636.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___100_15636.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____15637 = (FStar_TypeChecker_Rel.conj_guard g_ex guard1)
in ((e), (cres5), (uu____15637))))
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
| uu____15638 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let uu____15673 = (FStar_Options.ml_ish ())
in (match (uu____15673) with
| true -> begin
false
end
| uu____15674 -> begin
(

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____15676 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____15676) with
| (formals, c) -> begin
(

let uu____15701 = (FStar_Syntax_Util.abs_formals lbdef)
in (match (uu____15701) with
| (actuals, uu____15711, uu____15712) -> begin
(match ((((FStar_List.length formals) < (Prims.parse_int "1")) || ((FStar_List.length actuals) < (Prims.parse_int "1")))) with
| true -> begin
(

let uu____15725 = (

let uu____15730 = (

let uu____15731 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____15732 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____15731 uu____15732)))
in ((FStar_Errors.Fatal_RecursiveFunctionLiteral), (uu____15730)))
in (FStar_Errors.raise_error uu____15725 lbtyp.FStar_Syntax_Syntax.pos))
end
| uu____15733 -> begin
(

let actuals1 = (

let uu____15735 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____15735 actuals))
in ((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____15755 -> begin
(

let uu____15756 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____15756))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____15773 -> begin
(

let uu____15774 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____15774))
end))
in (

let msg = (

let uu____15782 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____15783 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____15782 uu____15783 formals_msg actuals_msg)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_LetRecArgumentMismatch), (msg)) lbdef.FStar_Syntax_Syntax.pos))))
end
| uu____15784 -> begin
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

let uu____15790 = (FStar_List.fold_left (fun uu____15817 lb -> (match (uu____15817) with
| (lbs1, env1) -> begin
(

let uu____15837 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____15837) with
| (univ_vars1, t, check_t, guard) -> begin
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univ_vars1)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t1 = (match ((not (check_t))) with
| true -> begin
t
end
| uu____15859 -> begin
(

let env01 = (FStar_TypeChecker_Env.push_univ_vars env0 univ_vars1)
in (

let uu____15861 = (

let uu____15868 = (

let uu____15869 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15869))
in (tc_check_tot_or_gtot_term (

let uu___101_15880 = env01
in {FStar_TypeChecker_Env.solver = uu___101_15880.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___101_15880.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___101_15880.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___101_15880.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___101_15880.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___101_15880.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___101_15880.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___101_15880.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___101_15880.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___101_15880.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___101_15880.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___101_15880.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___101_15880.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___101_15880.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___101_15880.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___101_15880.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___101_15880.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___101_15880.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___101_15880.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___101_15880.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___101_15880.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___101_15880.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___101_15880.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___101_15880.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___101_15880.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___101_15880.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___101_15880.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___101_15880.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___101_15880.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___101_15880.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___101_15880.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___101_15880.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___101_15880.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___101_15880.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___101_15880.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___101_15880.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___101_15880.FStar_TypeChecker_Env.dep_graph}) t uu____15868))
in (match (uu____15861) with
| (t1, uu____15882, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.resolve_implicits env2 g)
in ((

let uu____15886 = (FStar_TypeChecker_Rel.discharge_guard env2 g1)
in (FStar_All.pipe_left (fun a238 -> ()) uu____15886));
(norm env01 t1);
))
end)))
end)
in (

let env3 = (

let uu____15888 = (termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1)
in (match (uu____15888) with
| true -> begin
(

let uu___102_15889 = env2
in {FStar_TypeChecker_Env.solver = uu___102_15889.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___102_15889.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___102_15889.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___102_15889.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___102_15889.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___102_15889.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___102_15889.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___102_15889.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___102_15889.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___102_15889.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___102_15889.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___102_15889.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___102_15889.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1), (univ_vars1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___102_15889.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___102_15889.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___102_15889.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___102_15889.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___102_15889.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___102_15889.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___102_15889.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___102_15889.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___102_15889.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___102_15889.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___102_15889.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___102_15889.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___102_15889.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___102_15889.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___102_15889.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___102_15889.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___102_15889.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___102_15889.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___102_15889.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___102_15889.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___102_15889.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___102_15889.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___102_15889.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___102_15889.FStar_TypeChecker_Env.dep_graph})
end
| uu____15900 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname ((univ_vars1), (t1)))
end))
in (

let lb1 = (

let uu___103_15906 = lb
in {FStar_Syntax_Syntax.lbname = uu___103_15906.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___103_15906.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___103_15906.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___103_15906.FStar_Syntax_Syntax.lbpos})
in (((lb1)::lbs1), (env3)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____15790) with
| (lbs1, env1) -> begin
(((FStar_List.rev lbs1)), (env1))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____15929 = (

let uu____15938 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____15964 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____15964) with
| (bs, t, lcomp) -> begin
(match (bs) with
| [] -> begin
(

let uu____15992 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_RecursiveFunctionLiteral), ("Only function literals may be defined recursively")) uu____15992))
end
| uu____15997 -> begin
(

let lb1 = (

let uu___104_16000 = lb
in (

let uu____16001 = (FStar_Syntax_Util.abs bs t lcomp)
in {FStar_Syntax_Syntax.lbname = uu___104_16000.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___104_16000.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___104_16000.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___104_16000.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____16001; FStar_Syntax_Syntax.lbattrs = uu___104_16000.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___104_16000.FStar_Syntax_Syntax.lbpos}))
in (

let uu____16004 = (

let uu____16011 = (FStar_TypeChecker_Env.set_expected_typ env lb1.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____16011 lb1.FStar_Syntax_Syntax.lbdef))
in (match (uu____16004) with
| (e, c, g) -> begin
((

let uu____16020 = (

let uu____16021 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____16021)))
in (match (uu____16020) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedGTotForLetRec), ("Expected let rec to be a Tot term; got effect GTot")) e.FStar_Syntax_Syntax.pos)
end
| uu____16022 -> begin
()
end));
(

let lb2 = (FStar_Syntax_Util.mk_letbinding lb1.FStar_Syntax_Syntax.lbname lb1.FStar_Syntax_Syntax.lbunivs lb1.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e lb1.FStar_Syntax_Syntax.lbattrs lb1.FStar_Syntax_Syntax.lbpos)
in ((lb2), (g)));
)
end)))
end)
end)))))
in (FStar_All.pipe_right uu____15938 FStar_List.unzip))
in (match (uu____15929) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____16070 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____16070) with
| (env1, uu____16088) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____16096 = (check_lbtyp top_level env lb)
in (match (uu____16096) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (Prims.op_disEquality univ_vars1 []))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UniversePolymorphicInnerLetBound), ("Inner let-bound definitions cannot be universe polymorphic")) e1.FStar_Syntax_Syntax.pos)
end
| uu____16135 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____16138 = (tc_maybe_toplevel_term (

let uu___105_16147 = env11
in {FStar_TypeChecker_Env.solver = uu___105_16147.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___105_16147.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___105_16147.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___105_16147.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___105_16147.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___105_16147.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___105_16147.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___105_16147.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___105_16147.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___105_16147.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___105_16147.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___105_16147.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___105_16147.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___105_16147.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___105_16147.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___105_16147.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___105_16147.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___105_16147.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___105_16147.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___105_16147.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___105_16147.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___105_16147.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___105_16147.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___105_16147.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___105_16147.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___105_16147.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___105_16147.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___105_16147.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___105_16147.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___105_16147.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___105_16147.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___105_16147.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___105_16147.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___105_16147.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___105_16147.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___105_16147.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___105_16147.FStar_TypeChecker_Env.dep_graph}) e11)
in (match (uu____16138) with
| (e12, c1, g1) -> begin
(

let uu____16161 = (

let uu____16166 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____16171 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____16166 e12 c1 wf_annot))
in (match (uu____16161) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____16186 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____16186) with
| true -> begin
(

let uu____16187 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____16188 = (FStar_Syntax_Print.lcomp_to_string c11)
in (

let uu____16189 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked let-bound def %s : %s guard is %s\n" uu____16187 uu____16188 uu____16189))))
end
| uu____16190 -> begin
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

let uu____16223 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____16223) with
| (univ_opening, univ_vars1) -> begin
(

let uu____16256 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in ((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____16256)))
end))
end
| uu____16261 -> begin
(

let uu____16262 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____16262) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____16311 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____16311)))
end
| uu____16316 -> begin
(

let uu____16317 = (FStar_Syntax_Util.type_u ())
in (match (uu____16317) with
| (k, uu____16337) -> begin
(

let uu____16338 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____16338) with
| (t2, uu____16360, g) -> begin
((

let uu____16363 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____16363) with
| true -> begin
(

let uu____16364 = (

let uu____16365 = (FStar_Syntax_Util.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____16365))
in (

let uu____16366 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____16364 uu____16366)))
end
| uu____16367 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____16369 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____16369))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____16375 -> (match (uu____16375) with
| (x, imp) -> begin
(

let uu____16394 = (FStar_Syntax_Util.type_u ())
in (match (uu____16394) with
| (tu, u) -> begin
((

let uu____16414 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____16414) with
| true -> begin
(

let uu____16415 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____16416 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____16417 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____16415 uu____16416 uu____16417))))
end
| uu____16418 -> begin
()
end));
(

let uu____16419 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____16419) with
| (t, uu____16439, g) -> begin
(

let x1 = (((

let uu___106_16447 = x
in {FStar_Syntax_Syntax.ppname = uu___106_16447.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___106_16447.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____16449 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____16449) with
| true -> begin
(

let uu____16450 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____16451 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____16450 uu____16451)))
end
| uu____16452 -> begin
()
end));
(

let uu____16453 = (push_binding env x1)
in ((x1), (uu____16453), (g), (u)));
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

let uu____16547 = (tc_binder env1 b)
in (match (uu____16547) with
| (b1, env', g, u) -> begin
(

let uu____16588 = (aux env' bs2)
in (match (uu____16588) with
| (bs3, env'1, g', us) -> begin
(

let uu____16641 = (

let uu____16642 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____16642))
in (((b1)::bs3), (env'1), (uu____16641), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____16731 uu____16732 -> (match (((uu____16731), (uu____16732))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____16801 = (tc_term env1 t)
in (match (uu____16801) with
| (t1, uu____16819, g') -> begin
(

let uu____16821 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____16821)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____16863 -> (match (uu____16863) with
| (pats1, g) -> begin
(

let uu____16888 = (tc_args env p)
in (match (uu____16888) with
| (args, g') -> begin
(

let uu____16901 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats1), (uu____16901)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____16914 = (tc_maybe_toplevel_term env e)
in (match (uu____16914) with
| (e1, c, g) -> begin
(

let uu____16930 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____16930) with
| true -> begin
((e1), (c), (g))
end
| uu____16937 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (FStar_Syntax_Syntax.lcomp_comp c)
in (

let c2 = (norm_c env c1)
in (

let uu____16941 = (

let uu____16946 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____16946) with
| true -> begin
(

let uu____16951 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____16951), (false)))
end
| uu____16952 -> begin
(

let uu____16953 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____16953), (true)))
end))
in (match (uu____16941) with
| (target_comp, allow_ghost) -> begin
(

let uu____16962 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____16962) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____16972 = (FStar_Syntax_Util.lcomp_of_comp target_comp)
in (

let uu____16973 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in ((e1), (uu____16972), (uu____16973))))
end
| uu____16974 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____16983 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in (FStar_Errors.raise_error uu____16983 e1.FStar_Syntax_Syntax.pos))
end
| uu____16994 -> begin
(

let uu____16995 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in (FStar_Errors.raise_error uu____16995 e1.FStar_Syntax_Syntax.pos))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____17018 = (tc_tot_or_gtot_term env t)
in (match (uu____17018) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____17050 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____17050) with
| true -> begin
(

let uu____17051 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____17051))
end
| uu____17052 -> begin
()
end));
(

let env1 = (

let uu___107_17054 = env
in {FStar_TypeChecker_Env.solver = uu___107_17054.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___107_17054.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___107_17054.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___107_17054.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___107_17054.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___107_17054.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___107_17054.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___107_17054.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___107_17054.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___107_17054.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___107_17054.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___107_17054.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___107_17054.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___107_17054.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___107_17054.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___107_17054.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___107_17054.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___107_17054.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___107_17054.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___107_17054.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___107_17054.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___107_17054.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___107_17054.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___107_17054.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___107_17054.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___107_17054.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___107_17054.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___107_17054.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___107_17054.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___107_17054.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___107_17054.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___107_17054.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___107_17054.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___107_17054.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___107_17054.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___107_17054.FStar_TypeChecker_Env.dep_graph})
in (

let uu____17061 = (FStar_All.try_with (fun uu___109_17075 -> (match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)) (fun uu___108_17087 -> (match (uu___108_17087) with
| FStar_Errors.Error (e1, msg, uu____17096) -> begin
(

let uu____17097 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((e1), (msg)) uu____17097))
end)))
in (match (uu____17061) with
| (t, c, g) -> begin
(

let uu____17113 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____17113) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____17120 -> begin
(

let uu____17121 = (

let uu____17126 = (

let uu____17127 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____17127))
in ((FStar_Errors.Fatal_UnexpectedImplictArgument), (uu____17126)))
in (

let uu____17128 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____17121 uu____17128)))
end))
end)));
))


let level_of_type_fail : 'Auu____17143 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  'Auu____17143 = (fun env e t -> (

let uu____17159 = (

let uu____17164 = (

let uu____17165 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____17165 t))
in ((FStar_Errors.Fatal_UnexpectedTermType), (uu____17164)))
in (

let uu____17166 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____17159 uu____17166))))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____17193 = (

let uu____17194 = (FStar_Syntax_Util.unrefine t1)
in uu____17194.FStar_Syntax_Syntax.n)
in (match (uu____17193) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____17198 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____17200 -> begin
(

let uu____17201 = (FStar_Syntax_Util.type_u ())
in (match (uu____17201) with
| (t_u, u) -> begin
(

let env1 = (

let uu___110_17209 = env
in {FStar_TypeChecker_Env.solver = uu___110_17209.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___110_17209.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___110_17209.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___110_17209.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___110_17209.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___110_17209.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___110_17209.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___110_17209.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___110_17209.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___110_17209.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___110_17209.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___110_17209.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___110_17209.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___110_17209.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___110_17209.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___110_17209.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___110_17209.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___110_17209.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___110_17209.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___110_17209.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___110_17209.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___110_17209.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___110_17209.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___110_17209.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___110_17209.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___110_17209.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___110_17209.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___110_17209.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___110_17209.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___110_17209.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___110_17209.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___110_17209.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___110_17209.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___110_17209.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___110_17209.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___110_17209.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___110_17209.FStar_TypeChecker_Env.dep_graph})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____17213 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____17213))
end
| uu____17214 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____17229 = (

let uu____17230 = (FStar_Syntax_Subst.compress e)
in uu____17230.FStar_Syntax_Syntax.n)
in (match (uu____17229) with
| FStar_Syntax_Syntax.Tm_bvar (uu____17233) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____17234) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____17259) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____17275) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
u.FStar_Syntax_Syntax.ctx_uvar_typ
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____17298) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____17305 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17305) with
| ((uu____17314, t), uu____17316) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____17322 = (FStar_Syntax_Util.unfold_lazy i)
in (universe_of_aux env uu____17322))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____17325, (FStar_Util.Inl (t), uu____17327), uu____17328) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____17375, (FStar_Util.Inr (c), uu____17377), uu____17378) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____17426) -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant env e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____17435; FStar_Syntax_Syntax.vars = uu____17436}, us) -> begin
(

let uu____17442 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17442) with
| ((us', t), uu____17453) -> begin
((match ((Prims.op_disEquality (FStar_List.length us) (FStar_List.length us'))) with
| true -> begin
(

let uu____17459 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), ("Unexpected number of universe instantiations")) uu____17459))
end
| uu____17460 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____17475 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____17476) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____17484) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____17507 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____17507) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____17525 -> (match (uu____17525) with
| (b, uu____17531) -> begin
(

let uu____17532 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____17532))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____17537 = (universe_of_aux env res)
in (level_of_type env res uu____17537)))
in (

let u_c = (

let uu____17539 = (FStar_TypeChecker_Env.effect_repr env c1 u_res)
in (match (uu____17539) with
| FStar_Pervasives_Native.None -> begin
u_res
end
| FStar_Pervasives_Native.Some (trepr) -> begin
(

let uu____17543 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____17543))
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
| FStar_Syntax_Syntax.Tm_bvar (uu____17642) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____17657) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____17696) -> begin
(

let uu____17697 = (universe_of_aux env hd3)
in ((uu____17697), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____17706) -> begin
(

let uu____17707 = (universe_of_aux env hd3)
in ((uu____17707), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____17716) -> begin
(

let uu____17717 = (universe_of_aux env hd3)
in ((uu____17717), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____17726) -> begin
(

let uu____17733 = (universe_of_aux env hd3)
in ((uu____17733), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____17742) -> begin
(

let uu____17769 = (universe_of_aux env hd3)
in ((uu____17769), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____17778) -> begin
(

let uu____17785 = (universe_of_aux env hd3)
in ((uu____17785), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____17794) -> begin
(

let uu____17795 = (universe_of_aux env hd3)
in ((uu____17795), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____17804) -> begin
(

let uu____17817 = (universe_of_aux env hd3)
in ((uu____17817), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____17826) -> begin
(

let uu____17833 = (universe_of_aux env hd3)
in ((uu____17833), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____17842) -> begin
(

let uu____17843 = (universe_of_aux env hd3)
in ((uu____17843), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____17852, (hd4)::uu____17854) -> begin
(

let uu____17919 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____17919) with
| (uu____17934, uu____17935, hd5) -> begin
(

let uu____17953 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____17953) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____18004 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env e)
in (

let uu____18006 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____18006) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____18057 -> begin
(

let uu____18058 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____18058) with
| (env1, uu____18080) -> begin
(

let env2 = (

let uu___111_18086 = env1
in {FStar_TypeChecker_Env.solver = uu___111_18086.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_18086.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_18086.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_18086.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___111_18086.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___111_18086.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_18086.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_18086.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_18086.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_18086.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_18086.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_18086.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_18086.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_18086.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___111_18086.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_18086.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_18086.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_18086.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___111_18086.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___111_18086.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___111_18086.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___111_18086.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___111_18086.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_18086.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___111_18086.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___111_18086.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___111_18086.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___111_18086.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___111_18086.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___111_18086.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___111_18086.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___111_18086.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___111_18086.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___111_18086.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___111_18086.FStar_TypeChecker_Env.dep_graph})
in ((

let uu____18088 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____18088) with
| true -> begin
(

let uu____18089 = (

let uu____18090 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____18090))
in (

let uu____18091 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____18089 uu____18091)))
end
| uu____18092 -> begin
()
end));
(

let uu____18093 = (tc_term env2 hd3)
in (match (uu____18093) with
| (uu____18114, {FStar_Syntax_Syntax.eff_name = uu____18115; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____18117; FStar_Syntax_Syntax.comp_thunk = uu____18118}, g) -> begin
((

let uu____18138 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____18138 (fun a239 -> ())));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____18149 = (type_of_head true hd1 args)
in (match (uu____18149) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____18187 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____18187) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____18226 -> begin
(

let uu____18227 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____18227))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____18228, (hd1)::uu____18230) -> begin
(

let uu____18295 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____18295) with
| (uu____18296, uu____18297, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____18315, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____18360 = (universe_of_aux env e)
in (level_of_type env e uu____18360)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____18383 = (tc_binders env tps)
in (match (uu____18383) with
| (tps1, env1, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
((tps1), (env1), (us));
)
end)))


let rec type_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env t -> (

let mk_tm_type = (fun u -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____18437 = (

let uu____18438 = (FStar_Syntax_Subst.compress t)
in uu____18438.FStar_Syntax_Syntax.n)
in (match (uu____18437) with
| FStar_Syntax_Syntax.Tm_delayed (uu____18443) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____18470) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____18475 = (FStar_Syntax_Util.unfold_lazy i)
in (type_of_well_typed_term env uu____18475))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____18477 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env [] fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____18477 (fun uu____18491 -> (match (uu____18491) with
| (t1, uu____18499) -> begin
FStar_Pervasives_Native.Some (t1)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____18501; FStar_Syntax_Syntax.vars = uu____18502}, us) -> begin
(

let uu____18508 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env us fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____18508 (fun uu____18522 -> (match (uu____18522) with
| (t1, uu____18530) -> begin
FStar_Pervasives_Native.Some (t1)
end))))
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(

let uu____18532 = (tc_constant env t.FStar_Syntax_Syntax.pos sc)
in FStar_Pervasives_Native.Some (uu____18532))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____18534 = (mk_tm_type (FStar_Syntax_Syntax.U_succ (u)))
in FStar_Pervasives_Native.Some (uu____18534))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = eff; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (tbody); FStar_Syntax_Syntax.residual_flags = uu____18539})) -> begin
(

let mk_comp = (

let uu____18579 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____18579) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_Total')
end
| uu____18606 -> begin
(

let uu____18607 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____18607) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_GTotal')
end
| uu____18630 -> begin
FStar_Pervasives_Native.None
end))
end))
in (FStar_Util.bind_opt mk_comp (fun f -> (

let uu____18670 = (universe_of_well_typed_term env tbody)
in (FStar_Util.bind_opt uu____18670 (fun u -> (

let uu____18678 = (

let uu____18681 = (

let uu____18688 = (

let uu____18689 = (

let uu____18702 = (f tbody (FStar_Pervasives_Native.Some (u)))
in ((bs), (uu____18702)))
in FStar_Syntax_Syntax.Tm_arrow (uu____18689))
in (FStar_Syntax_Syntax.mk uu____18688))
in (uu____18681 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in FStar_Pervasives_Native.Some (uu____18678))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____18736 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____18736) with
| (bs1, c1) -> begin
(

let rec aux = (fun env1 us bs2 -> (match (bs2) with
| [] -> begin
(

let uu____18789 = (universe_of_well_typed_term env1 (FStar_Syntax_Util.comp_result c1))
in (FStar_Util.bind_opt uu____18789 (fun uc -> (

let uu____18797 = (mk_tm_type (FStar_Syntax_Syntax.U_max ((uc)::us)))
in FStar_Pervasives_Native.Some (uu____18797)))))
end
| ((x, imp))::bs3 -> begin
(

let uu____18815 = (universe_of_well_typed_term env1 x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____18815 (fun u_x -> (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x)
in (aux env2 ((u_x)::us) bs3)))))
end))
in (aux env [] bs1))
end))
end
| FStar_Syntax_Syntax.Tm_abs (uu____18824) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____18842) -> begin
(

let uu____18847 = (universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____18847 (fun u_x -> (

let uu____18855 = (mk_tm_type u_x)
in FStar_Pervasives_Native.Some (uu____18855)))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let t_hd = (type_of_well_typed_term env hd1)
in (

let rec aux = (fun t_hd1 -> (

let uu____18893 = (

let uu____18894 = (FStar_TypeChecker_Normalize.unfold_whnf env t_hd1)
in uu____18894.FStar_Syntax_Syntax.n)
in (match (uu____18893) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_bs = (FStar_List.length bs)
in (

let bs_t_opt = (match ((n_args < n_bs)) with
| true -> begin
(

let uu____18964 = (FStar_Util.first_N n_args bs)
in (match (uu____18964) with
| (bs1, rest) -> begin
(

let t1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None t_hd1.FStar_Syntax_Syntax.pos)
in (

let uu____19038 = (

let uu____19043 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Subst.open_comp bs1 uu____19043))
in (match (uu____19038) with
| (bs2, c1) -> begin
FStar_Pervasives_Native.Some (((bs2), ((FStar_Syntax_Util.comp_result c1))))
end)))
end))
end
| uu____19066 -> begin
(match ((Prims.op_Equality n_args n_bs)) with
| true -> begin
(

let uu____19087 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____19087) with
| (bs1, c1) -> begin
(

let uu____19106 = (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
in (match (uu____19106) with
| true -> begin
FStar_Pervasives_Native.Some (((bs1), ((FStar_Syntax_Util.comp_result c1))))
end
| uu____19127 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| uu____19138 -> begin
FStar_Pervasives_Native.None
end)
end)
in (FStar_Util.bind_opt bs_t_opt (fun uu____19164 -> (match (uu____19164) with
| (bs1, t1) -> begin
(

let subst1 = (FStar_List.map2 (fun b a -> FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), ((FStar_Pervasives_Native.fst a))))) bs1 args)
in (

let uu____19222 = (FStar_Syntax_Subst.subst subst1 t1)
in FStar_Pervasives_Native.Some (uu____19222)))
end))))))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____19224) -> begin
(aux x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____19230, uu____19231) -> begin
(aux t1)
end
| uu____19272 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_Util.bind_opt t_hd aux)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____19273, (FStar_Util.Inl (t1), uu____19275), uu____19276) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____19323, (FStar_Util.Inr (c), uu____19325), uu____19326) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
FStar_Pervasives_Native.Some (u.FStar_Syntax_Syntax.ctx_uvar_typ)
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.t_term)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____19381) -> begin
(type_of_well_typed_term env t1)
end
| FStar_Syntax_Syntax.Tm_match (uu____19386) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____19409) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (uu____19422) -> begin
FStar_Pervasives_Native.None
end))))
and universe_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun env t -> (

let uu____19433 = (type_of_well_typed_term env t)
in (match (uu____19433) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.pos = uu____19439; FStar_Syntax_Syntax.vars = uu____19440}) -> begin
FStar_Pervasives_Native.Some (u)
end
| uu____19443 -> begin
FStar_Pervasives_Native.None
end)))


let check_type_of_well_typed_term : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun must_total env t k -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let env2 = (

let uu___112_19468 = env1
in {FStar_TypeChecker_Env.solver = uu___112_19468.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___112_19468.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___112_19468.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___112_19468.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___112_19468.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___112_19468.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___112_19468.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___112_19468.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___112_19468.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___112_19468.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___112_19468.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___112_19468.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___112_19468.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___112_19468.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___112_19468.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___112_19468.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___112_19468.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___112_19468.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___112_19468.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___112_19468.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___112_19468.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___112_19468.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___112_19468.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___112_19468.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___112_19468.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___112_19468.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___112_19468.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___112_19468.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___112_19468.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___112_19468.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___112_19468.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___112_19468.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___112_19468.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___112_19468.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___112_19468.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___112_19468.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___112_19468.FStar_TypeChecker_Env.dep_graph})
in (

let slow_check = (fun uu____19474 -> (match (must_total) with
| true -> begin
(

let uu____19475 = (env2.FStar_TypeChecker_Env.type_of env2 t)
in (match (uu____19475) with
| (uu____19482, uu____19483, g) -> begin
g
end))
end
| uu____19485 -> begin
(

let uu____19486 = (env2.FStar_TypeChecker_Env.tc_term env2 t)
in (match (uu____19486) with
| (uu____19493, uu____19494, g) -> begin
g
end))
end))
in (

let uu____19496 = (

let uu____19497 = (FStar_Options.__temp_fast_implicits ())
in (FStar_All.pipe_left Prims.op_Negation uu____19497))
in (match (uu____19496) with
| true -> begin
(slow_check ())
end
| uu____19498 -> begin
(

let uu____19499 = (type_of_well_typed_term env2 t)
in (match (uu____19499) with
| FStar_Pervasives_Native.None -> begin
(slow_check ())
end
| FStar_Pervasives_Native.Some (k') -> begin
((

let uu____19504 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____19504) with
| true -> begin
(

let uu____19505 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____19506 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____19507 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____19508 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n" uu____19505 uu____19506 uu____19507 uu____19508)))))
end
| uu____19509 -> begin
()
end));
(

let b = (FStar_TypeChecker_Rel.subtype_nosmt env2 k' k)
in ((

let uu____19512 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____19512) with
| true -> begin
(

let uu____19513 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____19514 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____19515 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____19516 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n" uu____19513 (match (b) with
| true -> begin
"succeeded"
end
| uu____19517 -> begin
"failed"
end) uu____19514 uu____19515 uu____19516)))))
end
| uu____19518 -> begin
()
end));
(match (b) with
| true -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____19519 -> begin
(slow_check ())
end);
));
)
end))
end))))))




