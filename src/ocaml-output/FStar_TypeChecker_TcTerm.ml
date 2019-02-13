
open Prims
open FStar_Pervasives

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___357_6 = env
in {FStar_TypeChecker_Env.solver = uu___357_6.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___357_6.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___357_6.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___357_6.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___357_6.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___357_6.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___357_6.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___357_6.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___357_6.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___357_6.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___357_6.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___357_6.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___357_6.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___357_6.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___357_6.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___357_6.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___357_6.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___357_6.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___357_6.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___357_6.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___357_6.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___357_6.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___357_6.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___357_6.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___357_6.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___357_6.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___357_6.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___357_6.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___357_6.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___357_6.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___357_6.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___357_6.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___357_6.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___357_6.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___357_6.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___357_6.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___357_6.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___357_6.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___357_6.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___357_6.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___357_6.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___357_6.FStar_TypeChecker_Env.nbe}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___358_14 = env
in {FStar_TypeChecker_Env.solver = uu___358_14.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___358_14.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___358_14.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___358_14.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___358_14.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___358_14.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___358_14.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___358_14.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___358_14.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___358_14.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___358_14.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___358_14.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___358_14.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___358_14.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___358_14.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___358_14.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___358_14.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___358_14.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___358_14.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___358_14.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___358_14.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___358_14.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___358_14.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___358_14.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___358_14.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___358_14.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___358_14.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___358_14.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___358_14.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___358_14.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___358_14.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___358_14.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___358_14.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___358_14.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___358_14.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___358_14.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___358_14.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___358_14.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___358_14.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___358_14.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___358_14.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___358_14.FStar_TypeChecker_Env.nbe}))


let mk_lex_list : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v1 tl1 -> (

let r = (match ((Prims.op_Equality tl1.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
v1.FStar_Syntax_Syntax.pos
end
| uu____50 -> begin
(FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos tl1.FStar_Syntax_Syntax.pos)
end)
in (

let uu____52 = (

let uu____57 = (

let uu____58 = (FStar_Syntax_Syntax.as_arg v1)
in (

let uu____67 = (

let uu____78 = (FStar_Syntax_Syntax.as_arg tl1)
in (uu____78)::[])
in (uu____58)::uu____67))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____57))
in (uu____52 FStar_Pervasives_Native.None r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___350_121 -> (match (uu___350_121) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____126 -> begin
false
end))


let steps : 'Auu____135 . 'Auu____135  ->  FStar_TypeChecker_Env.step Prims.list = (fun env -> (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.NoFullNorm)::[])


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
((t), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____223 -> begin
(

let t1 = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____232 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t1)
in (

let uu____237 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____237) with
| FStar_Pervasives_Native.None -> begin
((t1), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t1)
end
| uu____253 -> begin
(

let fail1 = (fun uu____264 -> (

let msg = (match (head_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____268 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" uu____268))
end
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____272 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____274 = (FStar_TypeChecker_Normalize.term_to_string env head1)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" uu____272 uu____274)))
end)
in (

let uu____277 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_EscapedBoundVar), (msg)) uu____277))))
in (

let uu____283 = (

let uu____296 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____297 = (

let uu____298 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____298))
in (FStar_TypeChecker_Util.new_implicit_var "no escape" uu____296 env uu____297)))
in (match (uu____283) with
| (s, uu____313, g0) -> begin
(

let uu____327 = (FStar_TypeChecker_Rel.try_teq true env t1 s)
in (match (uu____327) with
| FStar_Pervasives_Native.Some (g) -> begin
(

let g1 = (

let uu____337 = (FStar_TypeChecker_Env.conj_guard g g0)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____337))
in ((s), (g1)))
end
| uu____338 -> begin
(fail1 ())
end))
end)))
end)
end))))
end))
in (aux false kt)))


let push_binding : 'Auu____349 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____349)  ->  FStar_TypeChecker_Env.env = (fun env b -> (FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v1 -> (

let uu____404 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____404) with
| true -> begin
s
end
| uu____407 -> begin
(FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), (v1))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags (fun uu____430 -> (

let uu____431 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Util.set_result_typ uu____431 t)))))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> e)


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> ((FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos "value_check_expected_typ" env guard);
(

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____490 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____490))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____493 = (

let uu____500 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____500) with
| FStar_Pervasives_Native.None -> begin
(((memo_tk e t)), (lc), (guard))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____510 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____510) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____524 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____524) with
| (e2, g) -> begin
((

let uu____538 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____538) with
| true -> begin
(

let uu____541 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____543 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____545 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____547 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____541 uu____543 uu____545 uu____547)))))
end
| uu____550 -> begin
()
end));
(

let msg = (

let uu____559 = (FStar_TypeChecker_Env.is_trivial_guard_formula g)
in (match (uu____559) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____572 -> begin
(FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Env.conj_guard g guard)
in (

let lc2 = (

let uu____590 = ((FStar_All.pipe_right tlc FStar_Util.is_left) && (FStar_TypeChecker_Util.should_return env (FStar_Pervasives_Native.Some (e2)) lc1))
in (match (uu____590) with
| true -> begin
(

let uu____598 = (

let uu____599 = (FStar_TypeChecker_Util.lcomp_univ_opt lc1)
in (FStar_TypeChecker_Util.return_value env uu____599 t1 e2))
in (FStar_All.pipe_right uu____598 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____602 -> begin
lc1
end))
in (

let uu____604 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc2 g1)
in (match (uu____604) with
| (lc3, g2) -> begin
(

let uu____617 = (set_lcomp_result lc3 t')
in (((memo_tk e2 t')), (uu____617), (g2)))
end)))));
)
end)))
end))
end))
in (match (uu____493) with
| (e1, lc1, g) -> begin
((e1), (lc1), (g))
end))));
))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____655 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____655) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____665 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____665) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt ec -> (

let uu____718 = ec
in (match (uu____718) with
| (e, c) -> begin
(

let tot_or_gtot = (fun c1 -> (

let uu____741 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____741) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c1))
end
| uu____744 -> begin
(

let uu____746 = (FStar_Syntax_Util.is_pure_or_ghost_comp c1)
in (match (uu____746) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c1))
end
| uu____749 -> begin
(failwith "Impossible: Expected pure_or_ghost comp")
end))
end)))
in (

let uu____752 = (match (copt) with
| FStar_Pervasives_Native.Some (uu____765) -> begin
((copt), (c))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____768 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Parser_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____771 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____771)))))
in (match (uu____768) with
| true -> begin
(

let uu____780 = (

let uu____783 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____783))
in ((uu____780), (c)))
end
| uu____786 -> begin
(

let uu____788 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____788) with
| true -> begin
(

let uu____797 = (tot_or_gtot c)
in ((FStar_Pervasives_Native.None), (uu____797)))
end
| uu____800 -> begin
(

let uu____802 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____802) with
| true -> begin
(

let uu____811 = (

let uu____814 = (tot_or_gtot c)
in FStar_Pervasives_Native.Some (uu____814))
in ((uu____811), (c)))
end
| uu____817 -> begin
((FStar_Pervasives_Native.None), (c))
end))
end))
end))
end)
in (match (uu____752) with
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

let uu____842 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e uu____842))
in (

let c4 = (FStar_Syntax_Syntax.lcomp_comp c3)
in ((

let uu____845 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Low)
in (match (uu____845) with
| true -> begin
(

let uu____849 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____851 = (FStar_Syntax_Print.comp_to_string c4)
in (

let uu____853 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n" uu____849 uu____851 uu____853))))
end
| uu____856 -> begin
()
end));
(

let uu____858 = (FStar_TypeChecker_Util.check_comp env e c4 expected_c)
in (match (uu____858) with
| (e1, uu____872, g) -> begin
(

let g1 = (

let uu____875 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____875 "could not prove post-condition" g))
in ((

let uu____878 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____878) with
| true -> begin
(

let uu____881 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____883 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect;\n\tguard is: %s\n" uu____881 uu____883)))
end
| uu____886 -> begin
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


let no_logical_guard : 'Auu____898 'Auu____899 . FStar_TypeChecker_Env.env  ->  ('Auu____898 * 'Auu____899 * FStar_TypeChecker_Env.guard_t)  ->  ('Auu____898 * 'Auu____899 * FStar_TypeChecker_Env.guard_t) = (fun env uu____921 -> (match (uu____921) with
| (te, kt, f) -> begin
(

let uu____931 = (FStar_TypeChecker_Env.guard_form f)
in (match (uu____931) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____939 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____945 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____939 uu____945)))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let uu____958 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____958) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "Expected type is None\n")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____963 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____963))
end)))


let rec get_pat_vars' : FStar_Syntax_Syntax.bv Prims.list  ->  Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun all andlist pats -> (

let pats1 = (FStar_Syntax_Util.unmeta pats)
in (

let uu____1005 = (FStar_Syntax_Util.head_and_args pats1)
in (match (uu____1005) with
| (head1, args) -> begin
(

let uu____1050 = (

let uu____1065 = (

let uu____1066 = (FStar_Syntax_Util.un_uinst head1)
in uu____1066.FStar_Syntax_Syntax.n)
in ((uu____1065), (args)))
in (match (uu____1050) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____1082) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
(match (andlist) with
| true -> begin
(FStar_Util.as_set all FStar_Syntax_Syntax.order_bv)
end
| uu____1106 -> begin
(FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____1109, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1110))))::((hd1, FStar_Pervasives_Native.None))::((tl1, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let hdvs = (get_pat_vars' all false hd1)
in (

let tlvs = (get_pat_vars' all andlist tl1)
in (match (andlist) with
| true -> begin
(FStar_Util.set_intersect hdvs tlvs)
end
| uu____1184 -> begin
(FStar_Util.set_union hdvs tlvs)
end)))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____1187, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1188))))::((pat, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
(FStar_Syntax_Free.names pat)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((subpats, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
(get_pat_vars' all true subpats)
end
| uu____1272 -> begin
(FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
end))
end))))
and get_pat_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun all pats -> (get_pat_vars' all false pats))


let check_pat_fvs : 'Auu____1303 . FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * 'Auu____1303) Prims.list  ->  unit = (fun rng env pats bs -> (

let pat_vars = (

let uu____1339 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in (

let uu____1346 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env pats)
in (get_pat_vars uu____1339 uu____1346)))
in (

let uu____1347 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____1374 -> (match (uu____1374) with
| (b, uu____1381) -> begin
(

let uu____1382 = (FStar_Util.set_mem b pat_vars)
in (not (uu____1382)))
end))))
in (match (uu____1347) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____1389) -> begin
(

let uu____1394 = (

let uu____1400 = (

let uu____1402 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____1402))
in ((FStar_Errors.Warning_PatternMissingBoundVar), (uu____1400)))
in (FStar_Errors.log_issue rng uu____1394))
end))))


let check_smt_pat : 'Auu____1417 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * 'Auu____1417) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  unit = (fun env t bs c -> (

let uu____1458 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____1458) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____1461; FStar_Syntax_Syntax.effect_name = uu____1462; FStar_Syntax_Syntax.result_typ = uu____1463; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____1467))::[]; FStar_Syntax_Syntax.flags = uu____1468}) -> begin
(check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs)
end
| uu____1529 -> begin
(failwith "Impossible")
end)
end
| uu____1531 -> begin
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

let uu___359_1592 = env
in {FStar_TypeChecker_Env.solver = uu___359_1592.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___359_1592.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___359_1592.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___359_1592.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___359_1592.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___359_1592.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___359_1592.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___359_1592.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___359_1592.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___359_1592.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___359_1592.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___359_1592.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___359_1592.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___359_1592.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___359_1592.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___359_1592.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___359_1592.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___359_1592.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___359_1592.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___359_1592.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___359_1592.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___359_1592.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___359_1592.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___359_1592.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___359_1592.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___359_1592.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___359_1592.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___359_1592.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___359_1592.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___359_1592.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___359_1592.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___359_1592.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___359_1592.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___359_1592.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___359_1592.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___359_1592.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___359_1592.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___359_1592.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___359_1592.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___359_1592.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___359_1592.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___359_1592.FStar_TypeChecker_Env.nbe})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> ((

let uu____1618 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1618) with
| true -> begin
(

let uu____1621 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (

let uu____1624 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "Building a decreases clause over (%s) and %s\n" uu____1621 uu____1624)))
end
| uu____1627 -> begin
()
end));
(

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____1658 -> (match (uu____1658) with
| (b, uu____1668) -> begin
(

let t = (

let uu____1674 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____1674))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____1677) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1678) -> begin
[]
end
| uu____1693 -> begin
(

let uu____1694 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____1694)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____1707 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____1707) with
| (head1, uu____1727) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____1755 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____1763 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___351_1772 -> (match (uu___351_1772) with
| FStar_Syntax_Syntax.DECREASES (uu____1774) -> begin
true
end
| uu____1778 -> begin
false
end))))
in (match (uu____1763) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____1785 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____1806 -> begin
(mk_lex_list xs)
end))
end)))));
))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____1835 -> (match (uu____1835) with
| (l, t, u_names) -> begin
(

let uu____1859 = (

let uu____1860 = (FStar_Syntax_Subst.compress t)
in uu____1860.FStar_Syntax_Syntax.n)
in (match (uu____1859) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____1919 -> (match (uu____1919) with
| (x, imp) -> begin
(

let uu____1938 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____1938) with
| true -> begin
(

let uu____1947 = (

let uu____1948 = (

let uu____1951 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____1951))
in (FStar_Syntax_Syntax.new_bv uu____1948 x.FStar_Syntax_Syntax.sort))
in ((uu____1947), (imp)))
end
| uu____1954 -> begin
((x), (imp))
end))
end))))
in (

let uu____1958 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____1958) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____1979 = (

let uu____1984 = (

let uu____1985 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____1994 = (

let uu____2005 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____2005)::[])
in (uu____1985)::uu____1994))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____1984))
in (uu____1979 FStar_Pervasives_Native.None r))
in (

let precedes2 = (FStar_TypeChecker_Util.label "Could not prove termination of this recursive call" r precedes1)
in (

let uu____2042 = (FStar_Util.prefix formals2)
in (match (uu____2042) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___360_2105 = last1
in (

let uu____2106 = (FStar_Syntax_Util.refine last1 precedes2)
in {FStar_Syntax_Syntax.ppname = uu___360_2105.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___360_2105.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2106}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____2142 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____2142) with
| true -> begin
(

let uu____2145 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____2147 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____2149 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____2145 uu____2147 uu____2149))))
end
| uu____2152 -> begin
()
end));
((l), (t'), (u_names));
))))
end)))))
end)))
end
| uu____2156 -> begin
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

let uu____2220 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1)
in (FStar_TypeChecker_Common.mk_by_tactic tactic uu____2220))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____2821 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____2821) with
| true -> begin
(

let uu____2824 = (

let uu____2826 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2826))
in (

let uu____2828 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____2830 = (

let uu____2832 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____2832))
in (FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____2824 uu____2828 uu____2830))))
end
| uu____2834 -> begin
()
end));
(

let uu____2836 = (FStar_Util.record_time (fun uu____2855 -> (tc_maybe_toplevel_term (

let uu___361_2858 = env
in {FStar_TypeChecker_Env.solver = uu___361_2858.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___361_2858.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___361_2858.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___361_2858.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___361_2858.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___361_2858.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___361_2858.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___361_2858.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___361_2858.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___361_2858.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___361_2858.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___361_2858.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___361_2858.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___361_2858.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___361_2858.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___361_2858.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___361_2858.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___361_2858.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___361_2858.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___361_2858.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___361_2858.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___361_2858.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___361_2858.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___361_2858.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___361_2858.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___361_2858.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___361_2858.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___361_2858.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___361_2858.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___361_2858.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___361_2858.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___361_2858.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___361_2858.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___361_2858.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___361_2858.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___361_2858.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___361_2858.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___361_2858.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___361_2858.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___361_2858.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___361_2858.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___361_2858.FStar_TypeChecker_Env.nbe}) e)))
in (match (uu____2836) with
| (r, ms) -> begin
((

let uu____2883 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____2883) with
| true -> begin
((

let uu____2887 = (

let uu____2889 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2889))
in (

let uu____2891 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____2893 = (

let uu____2895 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____2895))
in (

let uu____2896 = (FStar_Util.string_of_int ms)
in (FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n" uu____2887 uu____2891 uu____2893 uu____2896)))));
(

let uu____2899 = r
in (match (uu____2899) with
| (e1, uu____2907, uu____2908) -> begin
(

let uu____2909 = (

let uu____2911 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2911))
in (

let uu____2913 = (FStar_Syntax_Print.term_to_string e1)
in (

let uu____2915 = (

let uu____2917 = (FStar_Syntax_Subst.compress e1)
in (FStar_Syntax_Print.tag_of_term uu____2917))
in (FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____2909 uu____2913 uu____2915))))
end));
)
end
| uu____2919 -> begin
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
| uu____2931 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in (

let top = (FStar_Syntax_Subst.compress e)
in ((

let uu____2935 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____2935) with
| true -> begin
(

let uu____2938 = (

let uu____2940 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2940))
in (

let uu____2942 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____2944 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____2938 uu____2942 uu____2944))))
end
| uu____2947 -> begin
()
end));
(match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2955) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2985) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2992) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3005) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____3006) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3007) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____3008) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____3009) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3028) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____3043) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____3050) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_quoted (qt, qi) -> begin
(

let projl = (fun uu___352_3066 -> (match (uu___352_3066) with
| FStar_Util.Inl (x) -> begin
x
end
| FStar_Util.Inr (uu____3072) -> begin
(failwith "projl fail")
end))
in (

let non_trivial_antiquotes = (fun qi1 -> (

let is_name1 = (fun t -> (

let uu____3088 = (

let uu____3089 = (FStar_Syntax_Subst.compress t)
in uu____3089.FStar_Syntax_Syntax.n)
in (match (uu____3088) with
| FStar_Syntax_Syntax.Tm_name (uu____3093) -> begin
true
end
| uu____3095 -> begin
false
end)))
in (FStar_Util.for_some (fun uu____3105 -> (match (uu____3105) with
| (uu____3111, t) -> begin
(

let uu____3113 = (is_name1 t)
in (not (uu____3113)))
end)) qi1.FStar_Syntax_Syntax.antiquotes)))
in (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_static when (non_trivial_antiquotes qi) -> begin
(

let e0 = e
in (

let newbvs = (FStar_List.map (fun uu____3132 -> (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_term)) qi.FStar_Syntax_Syntax.antiquotes)
in (

let z = (FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs)
in (

let lbs = (FStar_List.map (fun uu____3175 -> (match (uu____3175) with
| ((bv, t), bv') -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None (FStar_Util.Inl (bv')) [] FStar_Syntax_Syntax.t_term FStar_Parser_Const.effect_Tot_lid t [] t.FStar_Syntax_Syntax.pos)
end)) z)
in (

let qi1 = (

let uu___362_3204 = qi
in (

let uu____3205 = (FStar_List.map (fun uu____3233 -> (match (uu____3233) with
| ((bv, uu____3249), bv') -> begin
(

let uu____3261 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____3261)))
end)) z)
in {FStar_Syntax_Syntax.qkind = uu___362_3204.FStar_Syntax_Syntax.qkind; FStar_Syntax_Syntax.antiquotes = uu____3205}))
in (

let nq = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e1 = (FStar_List.fold_left (fun t lb -> (

let uu____3276 = (

let uu____3283 = (

let uu____3284 = (

let uu____3298 = (

let uu____3301 = (

let uu____3302 = (

let uu____3309 = (projl lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____3309))
in (uu____3302)::[])
in (FStar_Syntax_Subst.close uu____3301 t))
in ((((false), ((lb)::[]))), (uu____3298)))
in FStar_Syntax_Syntax.Tm_let (uu____3284))
in (FStar_Syntax_Syntax.mk uu____3283))
in (uu____3276 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))) nq lbs)
in (tc_maybe_toplevel_term env1 e1))))))))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let aqs = qi.FStar_Syntax_Syntax.antiquotes
in (

let env_tm = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_term)
in (

let uu____3348 = (FStar_List.fold_right (fun uu____3384 uu____3385 -> (match (((uu____3384), (uu____3385))) with
| ((bv, tm), (aqs_rev, guard)) -> begin
(

let uu____3454 = (tc_term env_tm tm)
in (match (uu____3454) with
| (tm1, uu____3472, g) -> begin
(

let uu____3474 = (FStar_TypeChecker_Env.conj_guard g guard)
in (((((bv), (tm1)))::aqs_rev), (uu____3474)))
end))
end)) aqs (([]), (FStar_TypeChecker_Env.trivial_guard)))
in (match (uu____3348) with
| (aqs_rev, guard) -> begin
(

let qi1 = (

let uu___363_3516 = qi
in {FStar_Syntax_Syntax.qkind = uu___363_3516.FStar_Syntax_Syntax.qkind; FStar_Syntax_Syntax.antiquotes = (FStar_List.rev aqs_rev)})
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 tm (FStar_Util.Inl (FStar_Syntax_Syntax.t_term)) guard)))
end))))
end
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let c = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Tac_lid; FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_term; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.SOMETRIVIAL)::(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]})
in (

let uu____3535 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3535) with
| (env', uu____3549) -> begin
(

let uu____3554 = (tc_term (

let uu___364_3563 = env'
in {FStar_TypeChecker_Env.solver = uu___364_3563.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___364_3563.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___364_3563.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___364_3563.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___364_3563.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___364_3563.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___364_3563.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___364_3563.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___364_3563.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___364_3563.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___364_3563.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___364_3563.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___364_3563.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___364_3563.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___364_3563.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___364_3563.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___364_3563.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___364_3563.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___364_3563.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___364_3563.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___364_3563.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___364_3563.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___364_3563.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___364_3563.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___364_3563.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___364_3563.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___364_3563.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___364_3563.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___364_3563.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___364_3563.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___364_3563.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___364_3563.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___364_3563.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___364_3563.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___364_3563.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___364_3563.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___364_3563.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___364_3563.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___364_3563.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___364_3563.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___364_3563.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___364_3563.FStar_TypeChecker_Env.nbe}) qt)
in (match (uu____3554) with
| (qt1, uu____3572, uu____3573) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt1), (qi)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3579 = (

let uu____3586 = (

let uu____3591 = (FStar_Syntax_Util.lcomp_of_comp c)
in FStar_Util.Inr (uu____3591))
in (value_check_expected_typ env1 top uu____3586 FStar_TypeChecker_Env.trivial_guard))
in (match (uu____3579) with
| (t1, lc, g) -> begin
(

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((t1), (FStar_Syntax_Syntax.Meta_monadic_lift (((FStar_Parser_Const.effect_PURE_lid), (FStar_Parser_Const.effect_TAC_lid), (FStar_Syntax_Syntax.t_term))))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in ((t2), (lc), (g)))
end)))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = uu____3608; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____3609); FStar_Syntax_Syntax.ltyp = uu____3610; FStar_Syntax_Syntax.rng = uu____3611}) -> begin
(

let uu____3622 = (FStar_Syntax_Util.unlazy top)
in (tc_term env1 uu____3622))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(value_check_expected_typ env1 top (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp)) FStar_TypeChecker_Env.trivial_guard)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____3629 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____3629) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___365_3646 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___365_3646.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___365_3646.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___365_3646.FStar_TypeChecker_Env.implicits})
in (

let uu____3647 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____3647), (c), (g1))))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____3668 = (FStar_Syntax_Util.type_u ())
in (match (uu____3668) with
| (t, u) -> begin
(

let uu____3681 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____3681) with
| (e2, c, g) -> begin
(

let uu____3697 = (

let uu____3714 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3714) with
| (env2, uu____3738) -> begin
(tc_smt_pats env2 pats)
end))
in (match (uu____3697) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___366_3776 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___366_3776.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___366_3776.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___366_3776.FStar_TypeChecker_Env.implicits})
in (

let uu____3777 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3780 = (FStar_TypeChecker_Env.conj_guard g g'1)
in ((uu____3777), (c), (uu____3780)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____3786 = (

let uu____3787 = (FStar_Syntax_Subst.compress e1)
in uu____3787.FStar_Syntax_Syntax.n)
in (match (uu____3786) with
| FStar_Syntax_Syntax.Tm_let ((uu____3796, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____3798; FStar_Syntax_Syntax.lbtyp = uu____3799; FStar_Syntax_Syntax.lbeff = uu____3800; FStar_Syntax_Syntax.lbdef = e11; FStar_Syntax_Syntax.lbattrs = uu____3802; FStar_Syntax_Syntax.lbpos = uu____3803})::[]), e2) -> begin
(

let uu____3834 = (

let uu____3841 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (tc_term uu____3841 e11))
in (match (uu____3834) with
| (e12, c1, g1) -> begin
(

let uu____3851 = (tc_term env1 e2)
in (match (uu____3851) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.maybe_return_e2_and_bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 e21 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let attrs = (

let uu____3875 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____3875) with
| true -> begin
(FStar_Syntax_Util.inline_let_attr)::[]
end
| uu____3880 -> begin
[]
end))
in (

let e3 = (

let uu____3885 = (

let uu____3892 = (

let uu____3893 = (

let uu____3907 = (

let uu____3915 = (

let uu____3918 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_Syntax_Syntax.t_unit), (e13), (attrs), (e13.FStar_Syntax_Syntax.pos)))
in (uu____3918)::[])
in ((false), (uu____3915)))
in ((uu____3907), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____3893))
in (FStar_Syntax_Syntax.mk uu____3892))
in (uu____3885 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3945 = (FStar_TypeChecker_Env.conj_guard g1 g2)
in ((e5), (c), (uu____3945))))))))))
end))
end))
end
| uu____3946 -> begin
(

let uu____3947 = (tc_term env1 e1)
in (match (uu____3947) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____3969)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic_lift (uu____3981)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____4000 = (tc_term env1 e1)
in (match (uu____4000) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____4024) -> begin
(

let uu____4071 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4071) with
| (env0, uu____4085) -> begin
(

let uu____4090 = (tc_comp env0 expected_c)
in (match (uu____4090) with
| (expected_c1, uu____4104, g) -> begin
(

let uu____4106 = (

let uu____4113 = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result expected_c1) (FStar_TypeChecker_Env.set_expected_typ env0))
in (tc_term uu____4113 e1))
in (match (uu____4106) with
| (e2, c', g') -> begin
(

let uu____4123 = (

let uu____4130 = (

let uu____4135 = (FStar_Syntax_Syntax.lcomp_comp c')
in ((e2), (uu____4135)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____4130))
in (match (uu____4123) with
| (e3, expected_c2, g'') -> begin
(

let uu____4145 = (tc_tactic_opt env0 topt)
in (match (uu____4145) with
| (topt1, gtac) -> begin
(

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inr (expected_c2)), (topt1))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____4205 = (FStar_TypeChecker_Env.conj_guard g' g'')
in (FStar_TypeChecker_Env.conj_guard g uu____4205))
in (

let uu____4206 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____4206) with
| (e5, c, f2) -> begin
(

let final_guard = (

let uu____4223 = (FStar_TypeChecker_Env.conj_guard f f2)
in (wrap_guard_with_tactic_opt topt1 uu____4223))
in (

let uu____4224 = (FStar_TypeChecker_Env.conj_guard final_guard gtac)
in ((e5), (c), (uu____4224))))
end)))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____4228) -> begin
(

let uu____4275 = (FStar_Syntax_Util.type_u ())
in (match (uu____4275) with
| (k, u) -> begin
(

let uu____4288 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____4288) with
| (t1, uu____4302, f) -> begin
(

let uu____4304 = (tc_tactic_opt env1 topt)
in (match (uu____4304) with
| (topt1, gtac) -> begin
(

let uu____4323 = (

let uu____4330 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____4330 e1))
in (match (uu____4323) with
| (e2, c, g) -> begin
(

let uu____4340 = (

let uu____4345 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____4351 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____4345 e2 c f))
in (match (uu____4340) with
| (c1, f1) -> begin
(

let uu____4361 = (

let uu____4368 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (topt1))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____4368 c1))
in (match (uu____4361) with
| (e3, c2, f2) -> begin
(

let final_guard = (

let uu____4415 = (FStar_TypeChecker_Env.conj_guard g f2)
in (FStar_TypeChecker_Env.conj_guard f1 uu____4415))
in (

let final_guard1 = (wrap_guard_with_tactic_opt topt1 final_guard)
in (

let uu____4417 = (FStar_TypeChecker_Env.conj_guard final_guard1 gtac)
in ((e3), (c2), (uu____4417)))))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____4418; FStar_Syntax_Syntax.vars = uu____4419}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____4498 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4498) with
| (unary_op1, uu____4522) -> begin
(

let head1 = (

let uu____4550 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____4550))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4598; FStar_Syntax_Syntax.vars = uu____4599}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____4678 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4678) with
| (unary_op1, uu____4702) -> begin
(

let head1 = (

let uu____4730 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____4730))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4778)); FStar_Syntax_Syntax.pos = uu____4779; FStar_Syntax_Syntax.vars = uu____4780}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____4859 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4859) with
| (unary_op1, uu____4883) -> begin
(

let head1 = (

let uu____4911 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____4911))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____4959; FStar_Syntax_Syntax.vars = uu____4960}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____5056 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5056) with
| (unary_op1, uu____5080) -> begin
(

let head1 = (

let uu____5108 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a1)::(a2)::[])))) FStar_Pervasives_Native.None uu____5108))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____5164; FStar_Syntax_Syntax.vars = uu____5165}, ((e1, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____5203 = (

let uu____5210 = (

let uu____5211 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5211))
in (tc_term uu____5210 e1))
in (match (uu____5203) with
| (e2, c, g) -> begin
(

let uu____5235 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5235) with
| (head1, uu____5259) -> begin
(

let uu____5284 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((((e2), (FStar_Pervasives_Native.None)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____5317 = (

let uu____5318 = (

let uu____5319 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_Syntax_Syntax.mk_Total uu____5319))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5318))
in ((uu____5284), (uu____5317), (g))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____5320; FStar_Syntax_Syntax.vars = uu____5321}, ((t, FStar_Pervasives_Native.None))::((r, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____5374 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5374) with
| (head1, uu____5398) -> begin
(

let env' = (

let uu____5424 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_TypeChecker_Env.set_expected_typ env1 uu____5424))
in (

let uu____5425 = (tc_term env' r)
in (match (uu____5425) with
| (er, uu____5439, gr) -> begin
(

let uu____5441 = (tc_term env1 t)
in (match (uu____5441) with
| (t1, tt, gt1) -> begin
(

let g = (FStar_TypeChecker_Env.conj_guard gr gt1)
in (

let uu____5458 = (

let uu____5459 = (

let uu____5464 = (

let uu____5465 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____5474 = (

let uu____5485 = (FStar_Syntax_Syntax.as_arg r)
in (uu____5485)::[])
in (uu____5465)::uu____5474))
in (FStar_Syntax_Syntax.mk_Tm_app head1 uu____5464))
in (uu____5459 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in ((uu____5458), (tt), (g))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____5520; FStar_Syntax_Syntax.vars = uu____5521}, uu____5522) -> begin
(

let uu____5547 = (

let uu____5553 = (

let uu____5555 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____5555))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____5553)))
in (FStar_Errors.raise_error uu____5547 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____5565; FStar_Syntax_Syntax.vars = uu____5566}, uu____5567) -> begin
(

let uu____5592 = (

let uu____5598 = (

let uu____5600 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____5600))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____5598)))
in (FStar_Errors.raise_error uu____5592 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____5610; FStar_Syntax_Syntax.vars = uu____5611}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify), ("Qualifier on argument to reify is irrelevant and will be ignored")))
end
| uu____5656 -> begin
()
end);
(

let uu____5658 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5658) with
| (env0, uu____5672) -> begin
(

let uu____5677 = (tc_term env0 e1)
in (match (uu____5677) with
| (e2, c, g) -> begin
(

let uu____5693 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5693) with
| (reify_op, uu____5717) -> begin
(

let u_c = (env1.FStar_TypeChecker_Env.universe_of env1 c.FStar_Syntax_Syntax.res_typ)
in (

let ef = (

let uu____5744 = (FStar_Syntax_Syntax.lcomp_comp c)
in (FStar_Syntax_Util.comp_effect_name uu____5744))
in ((

let uu____5748 = (

let uu____5750 = (FStar_TypeChecker_Env.is_user_reifiable_effect env1 ef)
in (not (uu____5750)))
in (match (uu____5748) with
| true -> begin
(

let uu____5753 = (

let uu____5759 = (FStar_Util.format1 "Effect %s cannot be reified" ef.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____5759)))
in (FStar_Errors.raise_error uu____5753 e2.FStar_Syntax_Syntax.pos))
end
| uu____5763 -> begin
()
end));
(

let repr = (

let uu____5766 = (FStar_Syntax_Syntax.lcomp_comp c)
in (FStar_TypeChecker_Env.reify_comp env1 uu____5766 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____5803 = (FStar_TypeChecker_Env.is_total_effect env1 ef)
in (match (uu____5803) with
| true -> begin
(

let uu____5806 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____5806 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____5807 -> begin
(

let ct = {FStar_Syntax_Syntax.comp_univs = (u_c)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Dv_lid; FStar_Syntax_Syntax.result_typ = repr; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = []}
in (

let uu____5818 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_right uu____5818 FStar_Syntax_Util.lcomp_of_comp)))
end))
in (

let uu____5819 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____5819) with
| (e4, c2, g') -> begin
(

let uu____5835 = (FStar_TypeChecker_Env.conj_guard g g')
in ((e4), (c2), (uu____5835)))
end)))));
)))
end))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.pos = uu____5837; FStar_Syntax_Syntax.vars = uu____5838}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect), ("Qualifier on argument to reflect is irrelevant and will be ignored")))
end
| uu____5883 -> begin
()
end);
(

let uu____5886 = (

let uu____5888 = (FStar_TypeChecker_Env.is_user_reifiable_effect env1 l)
in (not (uu____5888)))
in (match (uu____5886) with
| true -> begin
(

let uu____5891 = (

let uu____5897 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____5897)))
in (FStar_Errors.raise_error uu____5891 e1.FStar_Syntax_Syntax.pos))
end
| uu____5901 -> begin
()
end));
(

let uu____5903 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5903) with
| (reflect_op, uu____5927) -> begin
(

let uu____5952 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____5952) with
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: user reifiable effect has no decl?")
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____5992 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5992) with
| (env_no_ex, topt) -> begin
(

let uu____6011 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____6031 = (

let uu____6038 = (

let uu____6039 = (

let uu____6056 = (

let uu____6067 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____6076 = (

let uu____6087 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____6087)::[])
in (uu____6067)::uu____6076))
in ((repr), (uu____6056)))
in FStar_Syntax_Syntax.Tm_app (uu____6039))
in (FStar_Syntax_Syntax.mk uu____6038))
in (uu____6031 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____6135 = (

let uu____6142 = (

let uu____6143 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____6143 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____6142 t))
in (match (uu____6135) with
| (t1, uu____6169, g) -> begin
(

let uu____6171 = (

let uu____6172 = (FStar_Syntax_Subst.compress t1)
in uu____6172.FStar_Syntax_Syntax.n)
in (match (uu____6171) with
| FStar_Syntax_Syntax.Tm_app (uu____6185, ((res, uu____6187))::((wp, uu____6189))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____6246 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____6011) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____6272 = (

let uu____6279 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____6279) with
| (e2, c, g) -> begin
((

let uu____6296 = (

let uu____6298 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____6298))
in (match (uu____6296) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 ((((FStar_Errors.Error_UnexpectedGTotComputation), ("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____6319 -> begin
()
end));
(

let uu____6321 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____6321) with
| FStar_Pervasives_Native.None -> begin
((

let uu____6332 = (

let uu____6342 = (

let uu____6350 = (

let uu____6352 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____6354 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____6352 uu____6354)))
in ((FStar_Errors.Error_UnexpectedInstance), (uu____6350), (e2.FStar_Syntax_Syntax.pos)))
in (uu____6342)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____6332));
(

let uu____6372 = (FStar_TypeChecker_Env.conj_guard g g0)
in ((e2), (uu____6372)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____6376 = (

let uu____6377 = (FStar_TypeChecker_Env.conj_guard g g0)
in (FStar_TypeChecker_Env.conj_guard g' uu____6377))
in ((e2), (uu____6376)))
end));
)
end))
in (match (uu____6272) with
| (e2, g) -> begin
(

let c = (

let uu____6393 = (

let uu____6394 = (

let uu____6395 = (

let uu____6396 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____6396)::[])
in (

let uu____6397 = (

let uu____6408 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6408)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____6395; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____6397; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____6394))
in (FStar_All.pipe_right uu____6393 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____6468 = (comp_check_expected_typ env1 e3 c)
in (match (uu____6468) with
| (e4, c1, g') -> begin
(

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_monadic (((c1.FStar_Syntax_Syntax.eff_name), (c1.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e4.FStar_Syntax_Syntax.pos)
in (

let uu____6491 = (FStar_TypeChecker_Env.conj_guard g' g)
in ((e5), (c1), (uu____6491))))
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

let uu____6530 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____6530) with
| (head2, args) -> begin
(tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, ((uu____6580, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6581))))::((tau, FStar_Pervasives_Native.None))::[]) when ((FStar_Syntax_Util.is_synth_by_tactic head1) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____6634 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____6634) with
| (head2, args) -> begin
(tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) when ((FStar_Syntax_Util.is_synth_by_tactic head1) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____6709 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::rest -> begin
(((((tau), (FStar_Pervasives_Native.None)))::[]), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
(((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b)))))::(((tau), (FStar_Pervasives_Native.None)))::[]), (rest))
end
| uu____6919 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: bad application")) top.FStar_Syntax_Syntax.pos)
end)
in (match (uu____6709) with
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

let uu____7038 = (

let uu____7039 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____7039 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7038 instantiate_both))
in ((

let uu____7055 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____7055) with
| true -> begin
(

let uu____7058 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____7060 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____7062 = (

let uu____7064 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right uu____7064 (fun uu___353_7071 -> (match (uu___353_7071) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) Checking app %s, expected type is %s\n" uu____7058 uu____7060 uu____7062))))
end
| uu____7078 -> begin
()
end));
(

let uu____7080 = (tc_term (no_inst env2) head1)
in (match (uu____7080) with
| (head2, chead, g_head) -> begin
(

let uu____7096 = (

let uu____7103 = (((not (env2.FStar_TypeChecker_Env.lax)) && (

let uu____7106 = (FStar_Options.lax ())
in (not (uu____7106)))) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____7103) with
| true -> begin
(

let uu____7115 = (

let uu____7122 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____7122))
in (match (uu____7115) with
| (e1, c, g) -> begin
((e1), (c), (g))
end))
end
| uu____7134 -> begin
(

let uu____7136 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env2 head2 chead g_head args uu____7136))
end))
in (match (uu____7096) with
| (e1, c, g) -> begin
(

let uu____7148 = (

let uu____7155 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____7155) with
| true -> begin
(

let uu____7164 = (FStar_TypeChecker_Util.maybe_instantiate env0 e1 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____7164) with
| (e2, res_typ, implicits) -> begin
(

let uu____7180 = (FStar_Syntax_Util.set_result_typ_lc c res_typ)
in ((e2), (uu____7180), (implicits)))
end))
end
| uu____7181 -> begin
((e1), (c), (FStar_TypeChecker_Env.trivial_guard))
end))
in (match (uu____7148) with
| (e2, c1, implicits) -> begin
((

let uu____7193 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____7193) with
| true -> begin
(

let uu____7196 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____7196))
end
| uu____7199 -> begin
()
end));
(

let uu____7201 = (comp_check_expected_typ env0 e2 c1)
in (match (uu____7201) with
| (e3, c2, g') -> begin
(

let gres = (FStar_TypeChecker_Env.conj_guard g g')
in (

let gres1 = (FStar_TypeChecker_Env.conj_guard gres implicits)
in ((

let uu____7220 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____7220) with
| true -> begin
(

let uu____7223 = (FStar_Syntax_Print.term_to_string e3)
in (

let uu____7225 = (FStar_TypeChecker_Rel.guard_to_string env2 gres1)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____7223 uu____7225)))
end
| uu____7228 -> begin
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

let uu____7268 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____7268) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____7288 = (tc_term env12 e1)
in (match (uu____7288) with
| (e11, c1, g1) -> begin
(

let uu____7304 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t), (g1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7318 = (FStar_Syntax_Util.type_u ())
in (match (uu____7318) with
| (k, uu____7330) -> begin
(

let uu____7331 = (FStar_TypeChecker_Util.new_implicit_var "match result" e.FStar_Syntax_Syntax.pos env1 k)
in (match (uu____7331) with
| (res_t, uu____7352, g) -> begin
(

let uu____7366 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in (

let uu____7367 = (FStar_TypeChecker_Env.conj_guard g1 g)
in ((uu____7366), (res_t), (uu____7367))))
end))
end))
end)
in (match (uu____7304) with
| (env_branches, res_t, g11) -> begin
((

let uu____7378 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____7378) with
| true -> begin
(

let uu____7381 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____7381))
end
| uu____7384 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____7508 = (

let uu____7513 = (FStar_List.fold_right (fun uu____7595 uu____7596 -> (match (((uu____7595), (uu____7596))) with
| ((branch1, f, eff_label, cflags, c, g), (caccum, gaccum)) -> begin
(

let uu____7841 = (FStar_TypeChecker_Env.conj_guard g gaccum)
in (((((f), (eff_label), (cflags), (c)))::caccum), (uu____7841)))
end)) t_eqns (([]), (FStar_TypeChecker_Env.trivial_guard)))
in (match (uu____7513) with
| (cases, g) -> begin
(

let uu____7946 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____7946), (g)))
end))
in (match (uu____7508) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____8088 -> (match (uu____8088) with
| ((pat, wopt, br), uu____8133, eff_label, uu____8135, uu____8136, uu____8137) -> begin
(

let uu____8174 = (FStar_TypeChecker_Util.maybe_lift env1 br eff_label cres.FStar_Syntax_Syntax.eff_name res_t)
in ((pat), (wopt), (uu____8174)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____8241 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____8241) with
| true -> begin
(mk_match e11)
end
| uu____8244 -> begin
(

let e_match = (

let uu____8249 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____8249))
in (

let lb = (

let uu____8253 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (guard_x)) [] c1.FStar_Syntax_Syntax.res_typ uu____8253 e11 [] e11.FStar_Syntax_Syntax.pos))
in (

let e2 = (

let uu____8259 = (

let uu____8266 = (

let uu____8267 = (

let uu____8281 = (

let uu____8284 = (

let uu____8285 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____8285)::[])
in (FStar_Syntax_Subst.close uu____8284 e_match))
in ((((false), ((lb)::[]))), (uu____8281)))
in FStar_Syntax_Syntax.Tm_let (uu____8267))
in (FStar_Syntax_Syntax.mk uu____8266))
in (uu____8259 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____8321 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____8321) with
| true -> begin
(

let uu____8324 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____8326 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____8324 uu____8326)))
end
| uu____8329 -> begin
()
end));
(

let uu____8331 = (FStar_TypeChecker_Env.conj_guard g11 g_branches)
in ((e2), (cres), (uu____8331)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8332); FStar_Syntax_Syntax.lbunivs = uu____8333; FStar_Syntax_Syntax.lbtyp = uu____8334; FStar_Syntax_Syntax.lbeff = uu____8335; FStar_Syntax_Syntax.lbdef = uu____8336; FStar_Syntax_Syntax.lbattrs = uu____8337; FStar_Syntax_Syntax.lbpos = uu____8338})::[]), uu____8339) -> begin
(check_top_level_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____8365), uu____8366) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8384); FStar_Syntax_Syntax.lbunivs = uu____8385; FStar_Syntax_Syntax.lbtyp = uu____8386; FStar_Syntax_Syntax.lbeff = uu____8387; FStar_Syntax_Syntax.lbdef = uu____8388; FStar_Syntax_Syntax.lbattrs = uu____8389; FStar_Syntax_Syntax.lbpos = uu____8390})::uu____8391), uu____8392) -> begin
(check_top_level_let_rec env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____8420), uu____8421) -> begin
(check_inner_let_rec env1 top)
end);
))))
and tc_synth : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun head1 env args rng -> (

let uu____8455 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::[] -> begin
((tau), (FStar_Pervasives_Native.None))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8494))))::((tau, FStar_Pervasives_Native.None))::[] -> begin
((tau), (FStar_Pervasives_Native.Some (a)))
end
| uu____8535 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: bad application")) rng)
end)
in (match (uu____8455) with
| (tau, atyp) -> begin
(

let typ = (match (atyp) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8568 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____8568) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8572 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: need a type annotation when no expected type is present")) uu____8572))
end))
end)
in (

let uu____8575 = (

let uu____8582 = (

let uu____8583 = (

let uu____8584 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8584))
in (FStar_TypeChecker_Env.set_expected_typ env uu____8583))
in (tc_term uu____8582 typ))
in (match (uu____8575) with
| (typ1, uu____8600, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let uu____8603 = (tc_tactic env tau)
in (match (uu____8603) with
| (tau1, uu____8617, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g2);
(

let t = (env.FStar_TypeChecker_Env.synth_hook env typ1 (

let uu___367_8622 = tau1
in {FStar_Syntax_Syntax.n = uu___367_8622.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___367_8622.FStar_Syntax_Syntax.vars}))
in ((

let uu____8624 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____8624) with
| true -> begin
(

let uu____8629 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____8629))
end
| uu____8632 -> begin
()
end));
(FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(

let uu____8635 = (

let uu____8636 = (FStar_Syntax_Syntax.mk_Total typ1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8636))
in ((t), (uu____8635), (FStar_TypeChecker_Env.trivial_guard)));
));
)
end));
)
end)))
end)))
and tc_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___368_8640 = env
in {FStar_TypeChecker_Env.solver = uu___368_8640.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___368_8640.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___368_8640.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___368_8640.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___368_8640.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___368_8640.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___368_8640.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___368_8640.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___368_8640.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___368_8640.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___368_8640.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___368_8640.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___368_8640.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___368_8640.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___368_8640.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___368_8640.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___368_8640.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___368_8640.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___368_8640.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___368_8640.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___368_8640.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___368_8640.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___368_8640.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___368_8640.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___368_8640.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___368_8640.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___368_8640.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___368_8640.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___368_8640.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___368_8640.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___368_8640.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___368_8640.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___368_8640.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___368_8640.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___368_8640.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___368_8640.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___368_8640.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___368_8640.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___368_8640.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___368_8640.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___368_8640.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___368_8640.FStar_TypeChecker_Env.nbe})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_TypeChecker_Env.guard_t) = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____8663 = (tc_tactic env tactic)
in (match (uu____8663) with
| (tactic1, uu____8677, g) -> begin
((FStar_Pervasives_Native.Some (tactic1)), (g))
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t0 -> (

let uu____8729 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0)
in (match (uu____8729) with
| (e2, t, implicits) -> begin
(

let tc = (

let uu____8750 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____8750) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____8757 -> begin
(

let uu____8759 = (

let uu____8760 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8760))
in FStar_Util.Inr (uu____8759))
end))
in (

let is_data_ctor = (fun uu___354_8769 -> (match (uu___354_8769) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____8774)) -> begin
true
end
| uu____8782 -> begin
false
end))
in (

let uu____8786 = ((is_data_ctor dc) && (

let uu____8789 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____8789))))
in (match (uu____8786) with
| true -> begin
(

let uu____8798 = (

let uu____8804 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingDataConstructor), (uu____8804)))
in (

let uu____8808 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____8798 uu____8808)))
end
| uu____8815 -> begin
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

let uu____8826 = (

let uu____8828 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____8828))
in (failwith uu____8826))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____8855 = (

let uu____8860 = (FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
in FStar_Util.Inl (uu____8860))
in (value_check_expected_typ env1 e uu____8855 FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____8862 = (

let uu____8875 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____8875) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8890 = (FStar_Syntax_Util.type_u ())
in (match (uu____8890) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Env.trivial_guard))
end))
in (match (uu____8862) with
| (t, uu____8928, g0) -> begin
(

let uu____8942 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____8942) with
| (e1, uu____8963, g1) -> begin
(

let uu____8977 = (

let uu____8978 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____8978 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____8979 = (FStar_TypeChecker_Env.conj_guard g0 g1)
in ((e1), (uu____8977), (uu____8979))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____8981 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____8991 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____8991)))
end
| uu____8992 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____8981) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___369_9005 = x
in {FStar_Syntax_Syntax.ppname = uu___369_9005.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___369_9005.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Env.insert_bv_info env1 x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____9008 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____9008) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____9029 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____9029) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____9036 -> begin
(

let uu____9038 = (

let uu____9039 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____9039))
in FStar_Util.Inr (uu____9038))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9041; FStar_Syntax_Syntax.vars = uu____9042}, uu____9043) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____9048 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____9048))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____9058 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____9058))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9068; FStar_Syntax_Syntax.vars = uu____9069}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____9078 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9078) with
| ((us', t), range) -> begin
((match ((Prims.op_disEquality (FStar_List.length us1) (FStar_List.length us'))) with
| true -> begin
(

let uu____9102 = (

let uu____9108 = (

let uu____9110 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____9112 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____9114 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____9110 uu____9112 uu____9114))))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____9108)))
in (

let uu____9118 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____9102 uu____9118)))
end
| uu____9119 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____9135 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____9140 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____9140 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____9142 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9142) with
| ((us, t), range) -> begin
((

let uu____9165 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____9165) with
| true -> begin
(

let uu____9170 = (

let uu____9172 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____9172))
in (

let uu____9173 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____9175 = (FStar_Range.string_of_range range)
in (

let uu____9177 = (FStar_Range.string_of_use_range range)
in (

let uu____9179 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____9170 uu____9173 uu____9175 uu____9177 uu____9179))))))
end
| uu____9182 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____9187 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____9187 us))
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

let uu____9215 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____9215) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____9229 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____9229) with
| (env2, uu____9243) -> begin
(

let uu____9248 = (tc_binders env2 bs1)
in (match (uu____9248) with
| (bs2, env3, g, us) -> begin
(

let uu____9267 = (tc_comp env3 c1)
in (match (uu____9267) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___370_9286 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___370_9286.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___370_9286.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____9297 = (FStar_TypeChecker_Env.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Env.conj_guard g uu____9297))
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

let uu____9313 = (

let uu____9318 = (

let uu____9319 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____9319)::[])
in (FStar_Syntax_Subst.open_term uu____9318 phi))
in (match (uu____9313) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____9347 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____9347) with
| (env2, uu____9361) -> begin
(

let uu____9366 = (

let uu____9381 = (FStar_List.hd x1)
in (tc_binder env2 uu____9381))
in (match (uu____9366) with
| (x2, env3, f1, u) -> begin
((

let uu____9417 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____9417) with
| true -> begin
(

let uu____9420 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____9422 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____9424 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____9420 uu____9422 uu____9424))))
end
| uu____9429 -> begin
()
end));
(

let uu____9431 = (FStar_Syntax_Util.type_u ())
in (match (uu____9431) with
| (t_phi, uu____9443) -> begin
(

let uu____9444 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____9444) with
| (phi2, uu____9458, f2) -> begin
(

let e1 = (

let uu___371_9463 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___371_9463.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___371_9463.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____9472 = (FStar_TypeChecker_Env.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Env.conj_guard f1 uu____9472))
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____9500) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____9527 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____9527) with
| true -> begin
(

let uu____9530 = (FStar_Syntax_Print.term_to_string (

let uu___372_9534 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.pos = uu___372_9534.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___372_9534.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____9530))
end
| uu____9548 -> begin
()
end));
(

let uu____9550 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____9550) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____9563 -> begin
(

let uu____9564 = (

let uu____9566 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____9568 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____9566 uu____9568)))
in (failwith uu____9564))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Syntax_Syntax.t_unit
end
| FStar_Const.Const_bool (uu____9580) -> begin
FStar_Syntax_Util.t_bool
end
| FStar_Const.Const_int (uu____9582, FStar_Pervasives_Native.None) -> begin
FStar_Syntax_Syntax.t_int
end
| FStar_Const.Const_int (uu____9595, FStar_Pervasives_Native.Some (msize)) -> begin
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
| FStar_Const.Const_string (uu____9613) -> begin
FStar_Syntax_Syntax.t_string
end
| FStar_Const.Const_float (uu____9619) -> begin
FStar_Syntax_Syntax.t_float
end
| FStar_Const.Const_char (uu____9620) -> begin
(

let uu____9622 = (FStar_Syntax_DsEnv.try_lookup_lid env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid)
in (FStar_All.pipe_right uu____9622 FStar_Util.must))
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____9627) -> begin
FStar_Syntax_Syntax.t_range
end
| FStar_Const.Const_range_of -> begin
(

let uu____9628 = (

let uu____9634 = (

let uu____9636 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____9636))
in ((FStar_Errors.Fatal_IllTyped), (uu____9634)))
in (FStar_Errors.raise_error uu____9628 r))
end
| FStar_Const.Const_set_range_of -> begin
(

let uu____9640 = (

let uu____9646 = (

let uu____9648 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____9648))
in ((FStar_Errors.Fatal_IllTyped), (uu____9646)))
in (FStar_Errors.raise_error uu____9640 r))
end
| FStar_Const.Const_reify -> begin
(

let uu____9652 = (

let uu____9658 = (

let uu____9660 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____9660))
in ((FStar_Errors.Fatal_IllTyped), (uu____9658)))
in (FStar_Errors.raise_error uu____9652 r))
end
| FStar_Const.Const_reflect (uu____9664) -> begin
(

let uu____9665 = (

let uu____9671 = (

let uu____9673 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____9673))
in ((FStar_Errors.Fatal_IllTyped), (uu____9671)))
in (FStar_Errors.raise_error uu____9665 r))
end
| uu____9677 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedConstant), ("Unsupported constant")) r)
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____9696) -> begin
(

let uu____9705 = (FStar_Syntax_Util.type_u ())
in (match (uu____9705) with
| (k, u) -> begin
(

let uu____9718 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____9718) with
| (t1, uu____9732, g) -> begin
(

let uu____9734 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____9734), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____9736) -> begin
(

let uu____9745 = (FStar_Syntax_Util.type_u ())
in (match (uu____9745) with
| (k, u) -> begin
(

let uu____9758 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____9758) with
| (t1, uu____9772, g) -> begin
(

let uu____9774 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____9774), (u), (g)))
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

let uu____9784 = (

let uu____9789 = (

let uu____9790 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____9790)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____9789))
in (uu____9784 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____9809 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____9809) with
| (tc1, uu____9823, f) -> begin
(

let uu____9825 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____9825) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____9875 = (

let uu____9876 = (FStar_Syntax_Subst.compress head3)
in uu____9876.FStar_Syntax_Syntax.n)
in (match (uu____9875) with
| FStar_Syntax_Syntax.Tm_uinst (uu____9879, us) -> begin
us
end
| uu____9885 -> begin
[]
end))
in (

let uu____9886 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____9886) with
| (uu____9909, args1) -> begin
(

let uu____9935 = (

let uu____9958 = (FStar_List.hd args1)
in (

let uu____9975 = (FStar_List.tl args1)
in ((uu____9958), (uu____9975))))
in (match (uu____9935) with
| (res, args2) -> begin
(

let uu____10056 = (

let uu____10065 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___355_10093 -> (match (uu___355_10093) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____10101 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____10101) with
| (env1, uu____10113) -> begin
(

let uu____10118 = (tc_tot_or_gtot_term env1 e)
in (match (uu____10118) with
| (e1, uu____10130, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Env.trivial_guard))
end))))
in (FStar_All.pipe_right uu____10065 FStar_List.unzip))
in (match (uu____10056) with
| (flags1, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___373_10171 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___373_10171.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___373_10171.FStar_Syntax_Syntax.flags}))
in (

let u_c = (FStar_All.pipe_right c2 (FStar_TypeChecker_Util.universe_of_comp env u))
in (

let uu____10177 = (FStar_List.fold_left FStar_TypeChecker_Env.conj_guard f guards)
in ((c2), (u_c), (uu____10177))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____10187) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____10191) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____10201 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____10201))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____10205 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____10205))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(

let uu____10209 = (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x))
in (match (uu____10209) with
| true -> begin
u2
end
| uu____10212 -> begin
(

let uu____10214 = (

let uu____10216 = (

let uu____10218 = (FStar_Syntax_Print.univ_to_string u2)
in (Prims.strcat uu____10218 " not found"))
in (Prims.strcat "Universe variable " uu____10216))
in (failwith uu____10214))
end))
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____10223 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____10225 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____10225 FStar_Pervasives_Native.snd))
end
| uu____10234 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail1 = (fun msg t -> (

let uu____10265 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in (FStar_Errors.raise_error uu____10265 top.FStar_Syntax_Syntax.pos)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____10354 bs2 bs_expected1 -> (match (uu____10354) with
| (env2, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ([]), (FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((

let special = (fun q1 q2 -> (match (((q1), (q2))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____10545)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____10546))) -> begin
true
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)) -> begin
true
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10561)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____10562))) -> begin
true
end
| uu____10571 -> begin
false
end))
in (

let uu____10581 = ((not ((special imp imp'))) && (

let uu____10584 = (FStar_Syntax_Util.eq_aqual imp imp')
in (Prims.op_disEquality uu____10584 FStar_Syntax_Util.Equal)))
in (match (uu____10581) with
| true -> begin
(

let uu____10586 = (

let uu____10592 = (

let uu____10594 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____10594))
in ((FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation), (uu____10592)))
in (

let uu____10598 = (FStar_Syntax_Syntax.range_of_bv hd1)
in (FStar_Errors.raise_error uu____10586 uu____10598)))
end
| uu____10599 -> begin
()
end)));
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____10602 = (

let uu____10609 = (

let uu____10610 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____10610.FStar_Syntax_Syntax.n)
in (match (uu____10609) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____10621 -> begin
((

let uu____10623 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____10623) with
| true -> begin
(

let uu____10626 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____10626))
end
| uu____10629 -> begin
()
end));
(

let uu____10631 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____10631) with
| (t, uu____10645, g1_env) -> begin
(

let g2_env = (

let uu____10648 = (FStar_TypeChecker_Rel.teq_nosmt_force env2 t expected_t)
in (match (uu____10648) with
| true -> begin
FStar_TypeChecker_Env.trivial_guard
end
| uu____10651 -> begin
(

let uu____10653 = (FStar_TypeChecker_Rel.get_subtyping_prop env2 expected_t t)
in (match (uu____10653) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10656 = (FStar_TypeChecker_Err.basic_type_error env2 FStar_Pervasives_Native.None expected_t t)
in (

let uu____10662 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____10656 uu____10662)))
end
| FStar_Pervasives_Native.Some (g_env) -> begin
(

let uu____10664 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_TypeChecker_Util.label_guard uu____10664 "Type annotation on parameter incompatible with the expected type" g_env))
end))
end))
in (

let uu____10666 = (FStar_TypeChecker_Env.conj_guard g1_env g2_env)
in ((t), (uu____10666))))
end));
)
end))
in (match (uu____10602) with
| (t, g_env) -> begin
(

let hd2 = (

let uu___374_10692 = hd1
in {FStar_Syntax_Syntax.ppname = uu___374_10692.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___374_10692.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env_b = (push_binding env2 b)
in (

let subst2 = (

let uu____10715 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____10715))
in (

let uu____10718 = (aux ((env_b), (subst2)) bs3 bs_expected2)
in (match (uu____10718) with
| (env_bs, bs4, rest, g'_env_b, subst3) -> begin
(

let g'_env = (FStar_TypeChecker_Env.close_guard env_bs ((b)::[]) g'_env_b)
in (

let uu____10783 = (FStar_TypeChecker_Env.conj_guard g_env g'_env)
in ((env_bs), ((b)::bs4), (rest), (uu____10783), (subst3))))
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
| uu____10955 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____10965 = (tc_binders env1 bs)
in (match (uu____10965) with
| (bs1, envbody, g_env, uu____10995) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody), (body1), (g_env))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____11051 = (

let uu____11052 = (FStar_Syntax_Subst.compress t2)
in uu____11052.FStar_Syntax_Syntax.n)
in (match (uu____11051) with
| FStar_Syntax_Syntax.Tm_uvar (uu____11085) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____11105 -> begin
(failwith "Impossible")
end);
(

let uu____11115 = (tc_binders env1 bs)
in (match (uu____11115) with
| (bs1, envbody, g_env, uu____11157) -> begin
(

let uu____11158 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____11158) with
| (envbody1, uu____11196) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g_env))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11217); FStar_Syntax_Syntax.pos = uu____11218; FStar_Syntax_Syntax.vars = uu____11219}, uu____11220) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____11264 -> begin
(failwith "Impossible")
end);
(

let uu____11274 = (tc_binders env1 bs)
in (match (uu____11274) with
| (bs1, envbody, g_env, uu____11316) -> begin
(

let uu____11317 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____11317) with
| (envbody1, uu____11355) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g_env))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____11377) -> begin
(

let uu____11382 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____11382) with
| (uu____11443, bs1, bs', copt, env_body, body2, g_env) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), (bs'), (copt), (env_body), (body2), (g_env))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____11520 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____11520) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 body2 -> (

let rec handle_more = (fun uu____11665 c_expected2 body3 -> (match (uu____11665) with
| (env_bs, bs2, more, guard_env, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11779 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env_bs), (bs2), (guard_env), (uu____11779), (body3)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____11796 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____11796))
in (

let uu____11797 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env_bs), (bs2), (guard_env), (uu____11797), (body3))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (

let uu____11814 = ((FStar_Options.ml_ish ()) || (FStar_Syntax_Util.is_named_tot c))
in (match (uu____11814) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env_bs (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____11880 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____11880) with
| (bs_expected4, c_expected4) -> begin
(

let uu____11907 = (check_binders env_bs more_bs bs_expected4)
in (match (uu____11907) with
| (env_bs_bs', bs', more1, guard'_env_bs, subst2) -> begin
(

let guard'_env = (FStar_TypeChecker_Env.close_guard env_bs bs2 guard'_env_bs)
in (

let uu____11962 = (

let uu____11989 = (FStar_TypeChecker_Env.conj_guard guard_env guard'_env)
in ((env_bs_bs'), ((FStar_List.append bs2 bs')), (more1), (uu____11989), (subst2)))
in (handle_more uu____11962 c_expected4 body3)))
end))
end))
end
| uu____12012 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env_bs), (bs2), (guard_env), (c), (body4)))
end))
end
| uu____12026 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env_bs), (bs2), (guard_env), (c), (body4)))
end)))
end)
end))
in (

let uu____12041 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____12041 c_expected1 body2))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___375_12106 = envbody
in {FStar_TypeChecker_Env.solver = uu___375_12106.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___375_12106.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___375_12106.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___375_12106.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___375_12106.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___375_12106.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___375_12106.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___375_12106.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___375_12106.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___375_12106.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___375_12106.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___375_12106.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___375_12106.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___375_12106.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___375_12106.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___375_12106.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___375_12106.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___375_12106.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___375_12106.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___375_12106.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___375_12106.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___375_12106.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___375_12106.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___375_12106.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___375_12106.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___375_12106.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___375_12106.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___375_12106.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___375_12106.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___375_12106.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___375_12106.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___375_12106.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___375_12106.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___375_12106.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___375_12106.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___375_12106.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___375_12106.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___375_12106.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___375_12106.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___375_12106.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___375_12106.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___375_12106.FStar_TypeChecker_Env.nbe})
in (

let uu____12113 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____12179 uu____12180 -> (match (((uu____12179), (uu____12180))) with
| ((env2, letrec_binders, g), (l, t3, u_names)) -> begin
(

let uu____12271 = (

let uu____12278 = (

let uu____12279 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____12279 FStar_Pervasives_Native.fst))
in (tc_term uu____12278 t3))
in (match (uu____12271) with
| (t4, uu____12303, g') -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l ((u_names), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____12316 = (FStar_Syntax_Syntax.mk_binder (

let uu___376_12319 = x
in {FStar_Syntax_Syntax.ppname = uu___376_12319.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___376_12319.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____12316)::letrec_binders)
end
| uu____12320 -> begin
letrec_binders
end)
in (

let uu____12325 = (FStar_TypeChecker_Env.conj_guard g g')
in ((env3), (lb), (uu____12325)))))
end))
end)) ((envbody1), ([]), (FStar_TypeChecker_Env.trivial_guard))))
in (match (uu____12113) with
| (envbody2, letrec_binders, g) -> begin
(

let uu____12345 = (FStar_TypeChecker_Env.close_guard envbody2 bs1 g)
in ((envbody2), (letrec_binders), (uu____12345)))
end)))))
in (

let uu____12348 = (check_actuals_against_formals env1 bs bs_expected1 body1)
in (match (uu____12348) with
| (envbody, bs1, g_env, c, body2) -> begin
(

let uu____12424 = (mk_letrec_env envbody bs1 c)
in (match (uu____12424) with
| (envbody1, letrecs, g_annots) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in (

let uu____12471 = (FStar_TypeChecker_Env.conj_guard g_env g_annots)
in ((FStar_Pervasives_Native.Some (t2)), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (envbody2), (body2), (uu____12471))))
end))
end))))
end))
end
| uu____12488 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____12520 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____12520))
end
| uu____12522 -> begin
(

let uu____12524 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____12524) with
| (uu____12573, bs1, uu____12575, c_opt, envbody, body2, g_env) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (c_opt), (envbody), (body2), (g_env))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____12607 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____12607) with
| (env1, topt) -> begin
((

let uu____12627 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____12627) with
| true -> begin
(

let uu____12630 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____12630 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____12639 -> begin
"false"
end)))
end
| uu____12642 -> begin
()
end));
(

let uu____12644 = (expected_function_typ1 env1 topt body)
in (match (uu____12644) with
| (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1, g_env) -> begin
((

let uu____12685 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("NYC")))
in (match (uu____12685) with
| true -> begin
(

let uu____12690 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____12693 = (FStar_TypeChecker_Rel.guard_to_string env1 g_env)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n" uu____12690 uu____12693)))
end
| uu____12696 -> begin
()
end));
(

let envbody1 = (FStar_TypeChecker_Env.set_range envbody body1.FStar_Syntax_Syntax.pos)
in (

let uu____12699 = (

let should_check_expected_effect = (

let uu____12712 = (

let uu____12719 = (

let uu____12720 = (FStar_Syntax_Subst.compress body1)
in uu____12720.FStar_Syntax_Syntax.n)
in ((c_opt), (uu____12719)))
in (match (uu____12712) with
| (FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Tm_ascribed (uu____12726, (FStar_Util.Inr (expected_c), uu____12728), uu____12729)) -> begin
false
end
| uu____12779 -> begin
true
end))
in (

let uu____12787 = (tc_term (

let uu___377_12796 = envbody1
in {FStar_TypeChecker_Env.solver = uu___377_12796.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___377_12796.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___377_12796.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___377_12796.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___377_12796.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___377_12796.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___377_12796.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___377_12796.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___377_12796.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___377_12796.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___377_12796.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___377_12796.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___377_12796.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___377_12796.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___377_12796.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___377_12796.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___377_12796.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___377_12796.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___377_12796.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___377_12796.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___377_12796.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___377_12796.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___377_12796.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___377_12796.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___377_12796.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___377_12796.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___377_12796.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___377_12796.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___377_12796.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___377_12796.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___377_12796.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___377_12796.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___377_12796.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___377_12796.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___377_12796.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___377_12796.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___377_12796.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___377_12796.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___377_12796.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___377_12796.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___377_12796.FStar_TypeChecker_Env.nbe}) body1)
in (match (uu____12787) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody1 guard_body)
in (match (should_check_expected_effect) with
| true -> begin
(

let uu____12823 = (

let uu____12830 = (

let uu____12835 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____12835)))
in (check_expected_effect (

let uu___378_12838 = envbody1
in {FStar_TypeChecker_Env.solver = uu___378_12838.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___378_12838.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___378_12838.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___378_12838.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___378_12838.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___378_12838.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___378_12838.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___378_12838.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___378_12838.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___378_12838.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___378_12838.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___378_12838.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___378_12838.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___378_12838.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___378_12838.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___378_12838.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___378_12838.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___378_12838.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___378_12838.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___378_12838.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___378_12838.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___378_12838.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___378_12838.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___378_12838.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___378_12838.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___378_12838.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___378_12838.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___378_12838.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___378_12838.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___378_12838.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___378_12838.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___378_12838.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___378_12838.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___378_12838.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___378_12838.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___378_12838.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___378_12838.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___378_12838.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___378_12838.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___378_12838.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___378_12838.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___378_12838.FStar_TypeChecker_Env.nbe}) c_opt uu____12830))
in (match (uu____12823) with
| (body3, cbody1, guard) -> begin
(

let uu____12852 = (FStar_TypeChecker_Env.conj_guard guard_body1 guard)
in ((body3), (cbody1), (uu____12852)))
end))
end
| uu____12857 -> begin
(

let uu____12859 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____12859), (guard_body1)))
end))
end)))
in (match (uu____12699) with
| (body2, cbody, guard_body) -> begin
(

let guard = (

let uu____12884 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____12887 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____12887))))
in (match (uu____12884) with
| true -> begin
(

let uu____12890 = (FStar_TypeChecker_Rel.discharge_guard env1 g_env)
in (

let uu____12891 = (FStar_TypeChecker_Rel.discharge_guard envbody1 guard_body)
in (FStar_TypeChecker_Env.conj_guard uu____12890 uu____12891)))
end
| uu____12892 -> begin
(

let guard = (

let uu____12895 = (FStar_TypeChecker_Env.close_guard env1 (FStar_List.append bs1 letrec_binders) guard_body)
in (FStar_TypeChecker_Env.conj_guard g_env uu____12895))
in guard)
end))
in (

let guard1 = (FStar_TypeChecker_Util.close_guard_implicits env1 bs1 guard)
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody)
in (

let e = (FStar_Syntax_Util.abs bs1 body2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody c_opt)))))
in (

let uu____12909 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____12930) -> begin
((e), (t1), (guard1))
end
| uu____12945 -> begin
(

let uu____12946 = (FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
in (match (uu____12946) with
| (e1, guard') -> begin
(

let uu____12959 = (FStar_TypeChecker_Env.conj_guard guard1 guard')
in ((e1), (t1), (uu____12959)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard1))
end)
in (match (uu____12909) with
| (e1, tfun, guard2) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Total tfun)
in (

let uu____12970 = (

let uu____12975 = (FStar_Syntax_Util.lcomp_of_comp c)
in (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 uu____12975 guard2))
in (match (uu____12970) with
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

let uu____13024 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13024) with
| true -> begin
(

let uu____13027 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____13029 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____13027 uu____13029)))
end
| uu____13032 -> begin
()
end));
(

let monadic_application = (fun uu____13107 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____13107) with
| (head2, chead1, ghead1, cres) -> begin
(

let uu____13168 = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____13168) with
| (rt, g0) -> begin
(

let cres1 = (

let uu___379_13182 = cres
in {FStar_Syntax_Syntax.eff_name = uu___379_13182.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___379_13182.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___379_13182.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____13183 = (match (bs) with
| [] -> begin
(

let g = (

let uu____13199 = (FStar_TypeChecker_Env.conj_guard ghead1 guard)
in (FStar_All.pipe_left (FStar_TypeChecker_Env.conj_guard g0) uu____13199))
in ((cres1), (g)))
end
| uu____13200 -> begin
(

let g = (

let uu____13210 = (

let uu____13211 = (FStar_TypeChecker_Env.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____13211 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (FStar_TypeChecker_Env.conj_guard g0 uu____13210))
in (

let uu____13212 = (

let uu____13213 = (

let uu____13214 = (

let uu____13215 = (FStar_Syntax_Syntax.lcomp_comp cres1)
in (FStar_Syntax_Util.arrow bs uu____13215))
in (FStar_Syntax_Syntax.mk_Total uu____13214))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____13213))
in ((uu____13212), (g))))
end)
in (match (uu____13183) with
| (cres2, guard1) -> begin
((

let uu____13227 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____13227) with
| true -> begin
(

let uu____13230 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____13230))
end
| uu____13233 -> begin
()
end));
(

let cres3 = (

let head_is_pure_and_some_arg_is_effectful = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1) && (FStar_Util.for_some (fun uu____13250 -> (match (uu____13250) with
| (uu____13260, uu____13261, lc) -> begin
((

let uu____13269 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____13269))) || (FStar_TypeChecker_Util.should_not_inline_lc lc))
end)) arg_comps_rev))
in (

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (

let uu____13282 = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2) && head_is_pure_and_some_arg_is_effectful)
in (match (uu____13282) with
| true -> begin
((

let uu____13286 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13286) with
| true -> begin
(

let uu____13289 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: Return inserted in monadic application: %s\n" uu____13289))
end
| uu____13292 -> begin
()
end));
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2);
)
end
| uu____13294 -> begin
((

let uu____13297 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13297) with
| true -> begin
(

let uu____13300 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: No return inserted in monadic application: %s\n" uu____13300))
end
| uu____13303 -> begin
()
end));
cres2;
)
end))))
in (

let comp = (FStar_List.fold_left (fun out_c uu____13331 -> (match (uu____13331) with
| ((e, q), x, c) -> begin
((

let uu____13373 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13373) with
| true -> begin
(

let uu____13376 = (match (x) with
| FStar_Pervasives_Native.None -> begin
"_"
end
| FStar_Pervasives_Native.Some (x1) -> begin
(FStar_Syntax_Print.bv_to_string x1)
end)
in (

let uu____13381 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____13383 = (FStar_Syntax_Print.lcomp_to_string c)
in (FStar_Util.print3 "(b) Monadic app: Binding argument %s : %s of type (%s)\n" uu____13376 uu____13381 uu____13383))))
end
| uu____13386 -> begin
()
end));
(

let uu____13388 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____13388) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____13393 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end));
)
end)) cres3 arg_comps_rev)
in (

let comp1 = ((

let uu____13399 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13399) with
| true -> begin
(

let uu____13402 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print1 "(c) Monadic app: Binding head %s\n" uu____13402))
end
| uu____13405 -> begin
()
end));
(

let uu____13407 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1)
in (match (uu____13407) with
| true -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (head2)) chead1 ((FStar_Pervasives_Native.None), (comp)))
end
| uu____13412 -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
end));
)
in (

let comp2 = (FStar_TypeChecker_Util.subst_lcomp subst1 comp1)
in (

let shortcuts_evaluation_order = (

let uu____13419 = (

let uu____13420 = (FStar_Syntax_Subst.compress head2)
in uu____13420.FStar_Syntax_Syntax.n)
in (match (uu____13419) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____13425 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____13448 -> (match (uu____13448) with
| (arg, uu____13462, uu____13463) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ))))
end
| uu____13472 -> begin
(

let uu____13474 = (

let map_fun = (fun uu____13540 -> (match (uu____13540) with
| ((e, q), uu____13581, c) -> begin
((

let uu____13604 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13604) with
| true -> begin
(

let uu____13607 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____13609 = (FStar_Syntax_Print.lcomp_to_string c)
in (FStar_Util.print2 "For arg e=(%s) c=(%s)... " uu____13607 uu____13609)))
end
| uu____13612 -> begin
()
end));
(

let uu____13614 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____13614) with
| true -> begin
((

let uu____13640 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13640) with
| true -> begin
(FStar_Util.print_string "... not lifting\n")
end
| uu____13644 -> begin
()
end));
((FStar_Pervasives_Native.None), (((e), (q))));
)
end
| uu____13676 -> begin
(

let warn_effectful_args = ((FStar_TypeChecker_Util.must_erase_for_extraction env chead1.FStar_Syntax_Syntax.res_typ) && (

let uu____13681 = (

let uu____13683 = (

let uu____13684 = (FStar_Syntax_Util.un_uinst head2)
in uu____13684.FStar_Syntax_Syntax.n)
in (match (uu____13683) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____13689 = (FStar_Parser_Const.psconst "ignore")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____13689))
end
| uu____13691 -> begin
true
end))
in (not (uu____13681))))
in ((match (warn_effectful_args) with
| true -> begin
(

let uu____13695 = (

let uu____13701 = (

let uu____13703 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____13705 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format3 "Effectful argument %s (%s) to erased function %s, consider let binding it" uu____13703 c.FStar_Syntax_Syntax.eff_name.FStar_Ident.str uu____13705)))
in ((FStar_Errors.Warning_EffectfulArgumentToErasedFunction), (uu____13701)))
in (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos uu____13695))
end
| uu____13709 -> begin
()
end);
(

let uu____13712 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13712) with
| true -> begin
(FStar_Util.print_string "... lifting!\n")
end
| uu____13716 -> begin
()
end));
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____13720 = (

let uu____13729 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____13729), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____13720)))));
))
end));
)
end))
in (

let uu____13758 = (

let uu____13789 = (

let uu____13818 = (

let uu____13829 = (

let uu____13838 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____13838), (FStar_Pervasives_Native.None), (chead1)))
in (uu____13829)::arg_comps_rev)
in (FStar_List.map map_fun uu____13818))
in (FStar_All.pipe_left FStar_List.split uu____13789))
in (match (uu____13758) with
| (lifted_args, reverse_args) -> begin
(

let uu____14039 = (

let uu____14040 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____14040))
in (

let uu____14061 = (

let uu____14062 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____14062))
in ((lifted_args), (uu____14039), (uu____14061))))
end)))
in (match (uu____13474) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___356_14173 -> (match (uu___356_14173) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1 [] e1.FStar_Syntax_Syntax.pos)
in (

let letbinding = (

let uu____14234 = (

let uu____14241 = (

let uu____14242 = (

let uu____14256 = (

let uu____14259 = (

let uu____14260 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____14260)::[])
in (FStar_Syntax_Subst.close uu____14259 e))
in ((((false), ((lb)::[]))), (uu____14256)))
in FStar_Syntax_Syntax.Tm_let (uu____14242))
in (FStar_Syntax_Syntax.mk uu____14241))
in (uu____14234 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp2.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____14315 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp2 guard1)
in (match (uu____14315) with
| (comp3, g) -> begin
((

let uu____14333 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14333) with
| true -> begin
(

let uu____14336 = (FStar_Syntax_Print.term_to_string app)
in (

let uu____14338 = (FStar_Syntax_Print.lcomp_to_string comp3)
in (FStar_Util.print2 "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n" uu____14336 uu____14338)))
end
| uu____14341 -> begin
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

let rec tc_args = (fun head_info uu____14419 bs args1 -> (match (uu____14419) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____14558))))::rest, ((uu____14560, FStar_Pervasives_Native.None))::uu____14561) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____14622 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (match (uu____14622) with
| (t1, g_ex) -> begin
(

let uu____14635 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____14635) with
| (varg, uu____14656, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____14684 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____14684)))
in (

let guard = (FStar_List.fold_right FStar_TypeChecker_Env.conj_guard ((g_ex)::(g)::[]) implicits)
in (

let uu____14693 = (

let uu____14728 = (

let uu____14739 = (

let uu____14748 = (

let uu____14749 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____14749 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____14748)))
in (uu____14739)::outargs)
in ((subst2), (uu____14728), ((arg)::arg_rets), (guard), (fvs)))
in (tc_args head_info uu____14693 rest args1)))))
end))
end)))
end
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau))))::rest, ((uu____14795, FStar_Pervasives_Native.None))::uu____14796) -> begin
(

let tau1 = (FStar_Syntax_Subst.subst subst1 tau)
in (

let uu____14858 = (tc_tactic env tau1)
in (match (uu____14858) with
| (tau2, uu____14872, g_tau) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____14875 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (match (uu____14875) with
| (t1, g_ex) -> begin
(

let uu____14888 = (

let uu____14901 = (

let uu____14908 = (

let uu____14913 = (FStar_Dyn.mkdyn env)
in ((uu____14913), (tau2)))
in FStar_Pervasives_Native.Some (uu____14908))
in (FStar_TypeChecker_Env.new_implicit_var_aux "Instantiating meta argument in application" head1.FStar_Syntax_Syntax.pos env t1 FStar_Syntax_Syntax.Strict uu____14901))
in (match (uu____14888) with
| (varg, uu____14926, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____14954 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____14954)))
in (

let guard = (FStar_List.fold_right FStar_TypeChecker_Env.conj_guard ((g_ex)::(g)::(g_tau)::[]) implicits)
in (

let uu____14963 = (

let uu____14998 = (

let uu____15009 = (

let uu____15018 = (

let uu____15019 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____15019 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____15018)))
in (uu____15009)::outargs)
in ((subst2), (uu____14998), ((arg)::arg_rets), (guard), (fvs)))
in (tc_args head_info uu____14963 rest args1)))))
end))
end)))
end)))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (uu____15135, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____15136))) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InconsistentImplicitQualifier), ("Inconsistent implicit qualifier; cannot apply meta arguments, just use #")) e.FStar_Syntax_Syntax.pos)
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____15147)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____15148))) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____15156)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____15157))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____15172 -> begin
(

let uu____15181 = (

let uu____15187 = (

let uu____15189 = (FStar_Syntax_Print.aqual_to_string aqual)
in (

let uu____15191 = (FStar_Syntax_Print.aqual_to_string aq)
in (

let uu____15193 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____15195 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format4 "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s" uu____15189 uu____15191 uu____15193 uu____15195)))))
in ((FStar_Errors.Fatal_InconsistentImplicitQualifier), (uu____15187)))
in (FStar_Errors.raise_error uu____15181 e.FStar_Syntax_Syntax.pos))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let aqual1 = (FStar_Syntax_Subst.subst_imp subst1 aqual)
in (

let x1 = (

let uu___380_15202 = x
in {FStar_Syntax_Syntax.ppname = uu___380_15202.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___380_15202.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____15204 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____15204) with
| true -> begin
(

let uu____15207 = (FStar_Syntax_Print.bv_to_string x1)
in (

let uu____15209 = (FStar_Syntax_Print.term_to_string x1.FStar_Syntax_Syntax.sort)
in (

let uu____15211 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____15213 = (FStar_Syntax_Print.subst_to_string subst1)
in (

let uu____15215 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print5 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n" uu____15207 uu____15209 uu____15211 uu____15213 uu____15215))))))
end
| uu____15218 -> begin
()
end));
(

let uu____15220 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (match (uu____15220) with
| (targ1, g_ex) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___381_15235 = env1
in {FStar_TypeChecker_Env.solver = uu___381_15235.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___381_15235.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___381_15235.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___381_15235.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___381_15235.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___381_15235.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___381_15235.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___381_15235.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___381_15235.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___381_15235.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___381_15235.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___381_15235.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___381_15235.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___381_15235.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___381_15235.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___381_15235.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___381_15235.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual1); FStar_TypeChecker_Env.is_iface = uu___381_15235.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___381_15235.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___381_15235.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___381_15235.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___381_15235.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___381_15235.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___381_15235.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___381_15235.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___381_15235.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___381_15235.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___381_15235.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___381_15235.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___381_15235.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___381_15235.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___381_15235.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___381_15235.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___381_15235.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___381_15235.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___381_15235.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___381_15235.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___381_15235.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___381_15235.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___381_15235.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___381_15235.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___381_15235.FStar_TypeChecker_Env.nbe})
in ((

let uu____15237 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____15237) with
| true -> begin
(

let uu____15240 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____15242 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____15244 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____15240 uu____15242 uu____15244))))
end
| uu____15247 -> begin
()
end));
(

let uu____15249 = (tc_term env2 e)
in (match (uu____15249) with
| (e1, c, g_e) -> begin
(

let g1 = (

let uu____15266 = (FStar_TypeChecker_Env.conj_guard g g_e)
in (FStar_All.pipe_left (FStar_TypeChecker_Env.conj_guard g_ex) uu____15266))
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____15289 = (

let uu____15292 = (

let uu____15301 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____15301))
in (FStar_Pervasives_Native.fst uu____15292))
in ((uu____15289), (aq)))
in (

let uu____15310 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____15310) with
| true -> begin
(

let subst2 = (

let uu____15320 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____15320 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____15375 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
)))
end));
))));
)
end
| (uu____15419, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____15455) -> begin
(

let uu____15506 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____15506) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 solve ghead2 tres -> (

let tres1 = (

let uu____15562 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____15562 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____15593 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____15593) with
| (bs2, cres'1) -> begin
(

let head_info1 = (

let uu____15615 = (FStar_Syntax_Util.lcomp_of_comp cres'1)
in ((head2), (chead1), (ghead2), (uu____15615)))
in ((

let uu____15617 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____15617) with
| true -> begin
(FStar_Errors.log_issue tres1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_RedundantExplicitCurrying), ("Potentially redundant explicit currying of a function type")))
end
| uu____15622 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Env.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____15664 when (not (norm1)) -> begin
(

let rec norm_tres = (fun tres2 -> (

let tres3 = (FStar_TypeChecker_Normalize.unfold_whnf env tres2)
in (

let uu____15672 = (

let uu____15673 = (FStar_Syntax_Subst.compress tres3)
in uu____15673.FStar_Syntax_Syntax.n)
in (match (uu____15672) with
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____15676; FStar_Syntax_Syntax.index = uu____15677; FStar_Syntax_Syntax.sort = tres4}, uu____15679) -> begin
(norm_tres tres4)
end
| uu____15687 -> begin
tres3
end))))
in (

let uu____15688 = (norm_tres tres1)
in (aux true solve ghead2 uu____15688)))
end
| uu____15690 when (not (solve)) -> begin
(

let ghead3 = (FStar_TypeChecker_Rel.solve_deferred_constraints env ghead2)
in (aux norm1 true ghead3 tres1))
end
| uu____15693 -> begin
(

let uu____15694 = (

let uu____15700 = (

let uu____15702 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____15704 = (FStar_Util.string_of_int n_args)
in (

let uu____15712 = (FStar_Syntax_Print.term_to_string tres1)
in (FStar_Util.format3 "Too many arguments to function of type %s; got %s arguments, remaining type is %s" uu____15702 uu____15704 uu____15712))))
in ((FStar_Errors.Fatal_ToManyArgumentToFunction), (uu____15700)))
in (

let uu____15716 = (FStar_Syntax_Syntax.argpos arg)
in (FStar_Errors.raise_error uu____15694 uu____15716)))
end)))
in (aux false false ghead1 chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf guard -> (

let uu____15746 = (

let uu____15747 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____15747.FStar_Syntax_Syntax.n)
in (match (uu____15746) with
| FStar_Syntax_Syntax.Tm_uvar (uu____15756) -> begin
(

let uu____15769 = (FStar_List.fold_right (fun uu____15800 uu____15801 -> (match (uu____15801) with
| (bs, guard1) -> begin
(

let uu____15828 = (

let uu____15841 = (

let uu____15842 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15842 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____15841))
in (match (uu____15828) with
| (t, uu____15859, g) -> begin
(

let uu____15873 = (

let uu____15876 = (FStar_Syntax_Syntax.null_binder t)
in (uu____15876)::bs)
in (

let uu____15877 = (FStar_TypeChecker_Env.conj_guard g guard1)
in ((uu____15873), (uu____15877))))
end))
end)) args (([]), (guard)))
in (match (uu____15769) with
| (bs, guard1) -> begin
(

let uu____15894 = (

let uu____15901 = (

let uu____15914 = (

let uu____15915 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15915 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____15914))
in (match (uu____15901) with
| (t, uu____15932, g) -> begin
(

let uu____15946 = (FStar_Options.ml_ish ())
in (match (uu____15946) with
| true -> begin
(

let uu____15955 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____15958 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____15955), (uu____15958))))
end
| uu____15961 -> begin
(

let uu____15963 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____15966 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____15963), (uu____15966))))
end))
end))
in (match (uu____15894) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____15985 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____15985) with
| true -> begin
(

let uu____15989 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____15991 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____15993 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____15989 uu____15991 uu____15993))))
end
| uu____15996 -> begin
()
end));
(

let g = (

let uu____15999 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____15999))
in (

let uu____16000 = (FStar_TypeChecker_Env.conj_guard g guard2)
in (check_function_app bs_cres uu____16000)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____16001); FStar_Syntax_Syntax.pos = uu____16002; FStar_Syntax_Syntax.vars = uu____16003}, uu____16004) -> begin
(

let uu____16041 = (FStar_List.fold_right (fun uu____16072 uu____16073 -> (match (uu____16073) with
| (bs, guard1) -> begin
(

let uu____16100 = (

let uu____16113 = (

let uu____16114 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____16114 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____16113))
in (match (uu____16100) with
| (t, uu____16131, g) -> begin
(

let uu____16145 = (

let uu____16148 = (FStar_Syntax_Syntax.null_binder t)
in (uu____16148)::bs)
in (

let uu____16149 = (FStar_TypeChecker_Env.conj_guard g guard1)
in ((uu____16145), (uu____16149))))
end))
end)) args (([]), (guard)))
in (match (uu____16041) with
| (bs, guard1) -> begin
(

let uu____16166 = (

let uu____16173 = (

let uu____16186 = (

let uu____16187 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____16187 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____16186))
in (match (uu____16173) with
| (t, uu____16204, g) -> begin
(

let uu____16218 = (FStar_Options.ml_ish ())
in (match (uu____16218) with
| true -> begin
(

let uu____16227 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____16230 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____16227), (uu____16230))))
end
| uu____16233 -> begin
(

let uu____16235 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____16238 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____16235), (uu____16238))))
end))
end))
in (match (uu____16166) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____16257 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____16257) with
| true -> begin
(

let uu____16261 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16263 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____16265 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____16261 uu____16263 uu____16265))))
end
| uu____16268 -> begin
()
end));
(

let g = (

let uu____16271 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____16271))
in (

let uu____16272 = (FStar_TypeChecker_Env.conj_guard g guard2)
in (check_function_app bs_cres uu____16272)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____16295 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____16295) with
| (bs1, c1) -> begin
(

let head_info = (

let uu____16317 = (FStar_Syntax_Util.lcomp_of_comp c1)
in ((head1), (chead), (ghead), (uu____16317)))
in ((

let uu____16319 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____16319) with
| true -> begin
(

let uu____16322 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16324 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____16326 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____16329 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print4 "######tc_args of head %s @ %s with formals=%s and result type=%s\n" uu____16322 uu____16324 uu____16326 uu____16329)))))
end
| uu____16332 -> begin
()
end));
(tc_args head_info (([]), ([]), ([]), (guard), ([])) bs1 args);
))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____16375) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort guard)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____16381, uu____16382) -> begin
(check_function_app t guard)
end
| uu____16423 -> begin
(

let uu____16424 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in (FStar_Errors.raise_error uu____16424 head1.FStar_Syntax_Syntax.pos))
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

let uu____16507 = (FStar_List.fold_left2 (fun uu____16576 uu____16577 uu____16578 -> (match (((uu____16576), (uu____16577), (uu____16578))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((

let uu____16731 = (

let uu____16733 = (FStar_Syntax_Util.eq_aqual aq aq')
in (Prims.op_disEquality uu____16733 FStar_Syntax_Util.Equal))
in (match (uu____16731) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InconsistentImplicitQualifier), ("Inconsistent implicit qualifiers")) e.FStar_Syntax_Syntax.pos)
end
| uu____16737 -> begin
()
end));
(

let uu____16739 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____16739) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____16768 = (FStar_TypeChecker_Env.guard_of_guard_formula short)
in (FStar_TypeChecker_Env.imp_guard uu____16768 g))
in (

let ghost1 = (ghost || ((

let uu____16773 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____16773))) && (

let uu____16776 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____16776)))))
in (

let uu____16778 = (

let uu____16789 = (

let uu____16800 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____16800)::[])
in (FStar_List.append seen uu____16789))
in (

let uu____16833 = (FStar_TypeChecker_Env.conj_guard guard g1)
in ((uu____16778), (uu____16833), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____16507) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____16901 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____16901 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____16902 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____16904 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____16904) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____16921 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_pat : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env pat_t p0 -> (

let fail1 = (fun msg -> (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchedPatternType), (msg)) p0.FStar_Syntax_Syntax.p))
in (

let expected_pat_typ = (fun env1 pos scrutinee_t -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Util.unrefine t)
in (

let uu____17012 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____17012) with
| (head1, args) -> begin
(

let uu____17055 = (

let uu____17056 = (FStar_Syntax_Subst.compress head1)
in uu____17056.FStar_Syntax_Syntax.n)
in (match (uu____17055) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____17060; FStar_Syntax_Syntax.vars = uu____17061}, us) -> begin
(unfold_once t1 f us args)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(unfold_once t1 f [] args)
end
| uu____17068 -> begin
(match (norm1) with
| true -> begin
t1
end
| uu____17070 -> begin
(

let uu____17072 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.Unmeta)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env1 t1)
in (aux true uu____17072))
end)
end))
end))))
and unfold_once = (fun t f us args -> (

let uu____17090 = (FStar_TypeChecker_Env.is_type_constructor env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17090) with
| true -> begin
t
end
| uu____17093 -> begin
(

let uu____17095 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17095) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (head_def_ts) -> begin
(

let uu____17115 = (FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us)
in (match (uu____17115) with
| (uu____17120, head_def) -> begin
(

let t' = (FStar_Syntax_Syntax.mk_Tm_app head_def args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let t'1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::[]) env1 t')
in (aux false t'1)))
end))
end))
end)))
in (

let uu____17127 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::[]) env1 scrutinee_t)
in (aux false uu____17127))))
in (

let pat_typ_ok = (fun env1 pat_t1 scrutinee_t -> ((

let uu____17146 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Patterns")))
in (match (uu____17146) with
| true -> begin
(

let uu____17151 = (FStar_Syntax_Print.term_to_string pat_t1)
in (

let uu____17153 = (FStar_Syntax_Print.term_to_string scrutinee_t)
in (FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n" uu____17151 uu____17153)))
end
| uu____17156 -> begin
()
end));
(

let fail2 = (fun msg -> (

let msg1 = (

let uu____17173 = (FStar_Syntax_Print.term_to_string pat_t1)
in (

let uu____17175 = (FStar_Syntax_Print.term_to_string scrutinee_t)
in (FStar_Util.format3 "Type of pattern (%s) does not match type of scrutinee (%s)%s" uu____17173 uu____17175 msg)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchedPatternType), (msg1)) p0.FStar_Syntax_Syntax.p)))
in (

let uu____17179 = (FStar_Syntax_Util.head_and_args scrutinee_t)
in (match (uu____17179) with
| (head_s, args_s) -> begin
(

let pat_t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 pat_t1)
in (

let uu____17223 = (FStar_Syntax_Util.un_uinst head_s)
in (match (uu____17223) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (uu____17224); FStar_Syntax_Syntax.pos = uu____17225; FStar_Syntax_Syntax.vars = uu____17226} -> begin
(

let uu____17229 = (FStar_Syntax_Util.head_and_args pat_t2)
in (match (uu____17229) with
| (head_p, args_p) -> begin
(

let uu____17272 = (FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p head_s)
in (match (uu____17272) with
| true -> begin
(

let uu____17275 = (

let uu____17276 = (FStar_Syntax_Util.un_uinst head_p)
in uu____17276.FStar_Syntax_Syntax.n)
in (match (uu____17275) with
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
((

let uu____17281 = (

let uu____17283 = (

let uu____17285 = (FStar_Syntax_Syntax.lid_of_fv f)
in (FStar_TypeChecker_Env.is_type_constructor env1 uu____17285))
in (FStar_All.pipe_left Prims.op_Negation uu____17283))
in (match (uu____17281) with
| true -> begin
(fail2 "Pattern matching a non-inductive type")
end
| uu____17290 -> begin
()
end));
(match ((Prims.op_disEquality (FStar_List.length args_p) (FStar_List.length args_s))) with
| true -> begin
(fail2 "")
end
| uu____17311 -> begin
()
end);
(

let uu____17313 = (

let uu____17338 = (

let uu____17342 = (FStar_Syntax_Syntax.lid_of_fv f)
in (FStar_TypeChecker_Env.num_inductive_ty_params env1 uu____17342))
in (match (uu____17338) with
| FStar_Pervasives_Native.None -> begin
((args_p), (args_s))
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____17391 = (FStar_Util.first_N n1 args_p)
in (match (uu____17391) with
| (params_p, uu____17449) -> begin
(

let uu____17490 = (FStar_Util.first_N n1 args_s)
in (match (uu____17490) with
| (params_s, uu____17548) -> begin
((params_p), (params_s))
end))
end))
end))
in (match (uu____17313) with
| (params_p, params_s) -> begin
(FStar_List.fold_left2 (fun out uu____17677 uu____17678 -> (match (((uu____17677), (uu____17678))) with
| ((p, uu____17712), (s, uu____17714)) -> begin
(

let uu____17747 = (FStar_TypeChecker_Rel.teq_nosmt env1 p s)
in (match (uu____17747) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17750 = (

let uu____17752 = (FStar_Syntax_Print.term_to_string p)
in (

let uu____17754 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "; parameter %s <> parameter %s" uu____17752 uu____17754)))
in (fail2 uu____17750))
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
| uu____17759 -> begin
(fail2 "Pattern matching a non-inductive type")
end))
end
| uu____17761 -> begin
(

let uu____17763 = (

let uu____17765 = (FStar_Syntax_Print.term_to_string head_p)
in (

let uu____17767 = (FStar_Syntax_Print.term_to_string head_s)
in (FStar_Util.format2 "; head mismatch %s vs %s" uu____17765 uu____17767)))
in (fail2 uu____17763))
end))
end))
end
| uu____17770 -> begin
(

let uu____17771 = (FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t)
in (match (uu____17771) with
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

let uu____17808 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____17808) with
| (head1, args) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let uu____17872 = (FStar_TypeChecker_Env.lookup_datacon env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17872) with
| (us, t_f) -> begin
(

let uu____17889 = (FStar_Syntax_Util.arrow_formals t_f)
in (match (uu____17889) with
| (formals, t) -> begin
((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
(fail1 "Pattern is not a fully-applied data constructor")
end
| uu____17953 -> begin
()
end);
(

let rec aux = (fun uu____18018 formals1 args1 -> (match (uu____18018) with
| (subst1, args_out, bvs, guard) -> begin
(match (((formals1), (args1))) with
| ([], []) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_uinst head1 us)
in (

let pat_e = (FStar_Syntax_Syntax.mk_Tm_app head2 args_out FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____18163 = (FStar_Syntax_Subst.subst subst1 t)
in ((pat_e), (uu____18163), (bvs), (guard)))))
end
| (((f1, uu____18169))::formals2, ((a, imp_a))::args2) -> begin
(

let t_f1 = (FStar_Syntax_Subst.subst subst1 f1.FStar_Syntax_Syntax.sort)
in (

let uu____18227 = (

let uu____18248 = (

let uu____18249 = (FStar_Syntax_Subst.compress a)
in uu____18249.FStar_Syntax_Syntax.n)
in (match (uu____18248) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let x1 = (

let uu___382_18274 = x
in {FStar_Syntax_Syntax.ppname = uu___382_18274.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___382_18274.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_f1})
in (

let a1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((f1), (a1))))::subst1
in ((((a1), (imp_a))), (subst2), ((FStar_List.append bvs ((x1)::[]))), (FStar_TypeChecker_Env.trivial_guard)))))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____18297) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_expected_typ env1 t_f1)
in (

let uu____18311 = (tc_tot_or_gtot_term env2 a)
in (match (uu____18311) with
| (a1, uu____18339, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env2 g)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((f1), (a1))))::subst1
in ((((a1), (imp_a))), (subst2), (bvs), (g1))))
end)))
end
| uu____18363 -> begin
(fail1 "Not a simple pattern")
end))
in (match (uu____18227) with
| (a1, subst2, bvs1, g) -> begin
(

let uu____18425 = (

let uu____18448 = (FStar_TypeChecker_Env.conj_guard g guard)
in ((subst2), ((FStar_List.append args_out ((a1)::[]))), (bvs1), (uu____18448)))
in (aux uu____18425 formals2 args2))
end)))
end
| uu____18487 -> begin
(fail1 "Not a fully applued pattern")
end)
end))
in (aux (([]), ([]), ([]), (FStar_TypeChecker_Env.trivial_guard)) formals args));
)
end))
end))
end
| uu____18543 -> begin
(fail1 "Not a simple pattern")
end)
end)))
in (

let rec check_nested_pattern = (fun env1 p t -> ((

let uu____18592 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Patterns")))
in (match (uu____18592) with
| true -> begin
(

let uu____18597 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____18599 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checking pattern %s at type %s\n" uu____18597 uu____18599)))
end
| uu____18602 -> begin
()
end));
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____18614) -> begin
(

let uu____18621 = (

let uu____18623 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Impossible: Expected an undecorated pattern, got %s" uu____18623))
in (failwith uu____18621))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___383_18638 = x
in {FStar_Syntax_Syntax.ppname = uu___383_18638.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___383_18638.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____18639 = (FStar_Syntax_Syntax.bv_to_name x1)
in (((x1)::[]), (uu____18639), ((

let uu___384_18643 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___384_18643.FStar_Syntax_Syntax.p})), (FStar_TypeChecker_Env.trivial_guard))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___385_18646 = x
in {FStar_Syntax_Syntax.ppname = uu___385_18646.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___385_18646.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____18647 = (FStar_Syntax_Syntax.bv_to_name x1)
in (((x1)::[]), (uu____18647), ((

let uu___386_18651 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___386_18651.FStar_Syntax_Syntax.p})), (FStar_TypeChecker_Env.trivial_guard))))
end
| FStar_Syntax_Syntax.Pat_constant (uu____18652) -> begin
(

let uu____18653 = (FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p)
in (match (uu____18653) with
| (uu____18675, e_c, uu____18677, uu____18678) -> begin
(

let uu____18683 = (tc_tot_or_gtot_term env1 e_c)
in (match (uu____18683) with
| (e_c1, lc, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
(

let expected_t = (expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t)
in ((

let uu____18706 = (

let uu____18708 = (FStar_TypeChecker_Rel.teq_nosmt_force env1 lc.FStar_Syntax_Syntax.res_typ expected_t)
in (not (uu____18708)))
in (match (uu____18706) with
| true -> begin
(

let uu____18711 = (

let uu____18713 = (FStar_Syntax_Print.term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____18715 = (FStar_Syntax_Print.term_to_string expected_t)
in (FStar_Util.format2 "Type of pattern (%s) does not match type of scrutinee (%s)" uu____18713 uu____18715)))
in (fail1 uu____18711))
end
| uu____18718 -> begin
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

let simple_sub_pats = (FStar_List.map (fun uu____18773 -> (match (uu____18773) with
| (p1, b) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____18803) -> begin
((p1), (b))
end
| uu____18813 -> begin
(

let uu____18814 = (

let uu____18817 = (

let uu____18818 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_var (uu____18818))
in (FStar_Syntax_Syntax.withinfo uu____18817 p1.FStar_Syntax_Syntax.p))
in ((uu____18814), (b)))
end)
end)) sub_pats)
in (

let uu___387_18822 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), (simple_sub_pats))); FStar_Syntax_Syntax.p = uu___387_18822.FStar_Syntax_Syntax.p}))
in (

let sub_pats1 = (FStar_All.pipe_right sub_pats (FStar_List.filter (fun uu____18867 -> (match (uu____18867) with
| (x, uu____18877) -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____18885) -> begin
false
end
| uu____18893 -> begin
true
end)
end))))
in (

let uu____18895 = (FStar_TypeChecker_PatternUtils.pat_as_exp false env1 simple_pat)
in (match (uu____18895) with
| (simple_bvs, simple_pat_e, g0, simple_pat_elab) -> begin
((match ((Prims.op_disEquality (FStar_List.length simple_bvs) (FStar_List.length sub_pats1))) with
| true -> begin
(

let uu____18932 = (

let uu____18934 = (FStar_Range.string_of_range p.FStar_Syntax_Syntax.p)
in (

let uu____18936 = (FStar_Syntax_Print.pat_to_string simple_pat)
in (

let uu____18938 = (FStar_Util.string_of_int (FStar_List.length sub_pats1))
in (

let uu____18945 = (FStar_Util.string_of_int (FStar_List.length simple_bvs))
in (FStar_Util.format4 "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s" uu____18934 uu____18936 uu____18938 uu____18945)))))
in (failwith uu____18932))
end
| uu____18948 -> begin
()
end);
(

let uu____18950 = (

let uu____18959 = (type_of_simple_pat env1 simple_pat_e)
in (match (uu____18959) with
| (simple_pat_e1, simple_pat_t, simple_bvs1, guard) -> begin
(

let g' = (

let uu____18987 = (expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t)
in (pat_typ_ok env1 simple_pat_t uu____18987))
in (

let guard1 = (FStar_TypeChecker_Env.conj_guard guard g')
in ((

let uu____18990 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Patterns")))
in (match (uu____18990) with
| true -> begin
(

let uu____18995 = (FStar_Syntax_Print.term_to_string simple_pat_e1)
in (

let uu____18997 = (FStar_Syntax_Print.term_to_string simple_pat_t)
in (

let uu____18999 = (

let uu____19001 = (FStar_List.map (fun x -> (

let uu____19009 = (

let uu____19011 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____19013 = (

let uu____19015 = (

let uu____19017 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (Prims.strcat uu____19017 ")"))
in (Prims.strcat " : " uu____19015))
in (Prims.strcat uu____19011 uu____19013)))
in (Prims.strcat "(" uu____19009))) simple_bvs1)
in (FStar_All.pipe_right uu____19001 (FStar_String.concat " ")))
in (FStar_Util.print3 "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n" uu____18995 uu____18997 uu____18999))))
end
| uu____19028 -> begin
()
end));
((simple_pat_e1), (simple_bvs1), (guard1));
)))
end))
in (match (uu____18950) with
| (simple_pat_e1, simple_bvs1, g1) -> begin
(

let uu____19049 = (

let uu____19071 = (

let uu____19093 = (FStar_TypeChecker_Env.conj_guard g0 g1)
in ((env1), ([]), ([]), ([]), (uu____19093)))
in (FStar_List.fold_left2 (fun uu____19154 uu____19155 x -> (match (((uu____19154), (uu____19155))) with
| ((env2, bvs, pats, subst1, g), (p1, b)) -> begin
(

let expected_t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____19288 = (check_nested_pattern env2 p1 expected_t)
in (match (uu____19288) with
| (bvs_p, e_p, p2, g') -> begin
(

let env3 = (FStar_TypeChecker_Env.push_bvs env2 bvs_p)
in (

let uu____19329 = (FStar_TypeChecker_Env.conj_guard g g')
in ((env3), ((FStar_List.append bvs bvs_p)), ((FStar_List.append pats ((((p2), (b)))::[]))), ((FStar_Syntax_Syntax.NT (((x), (e_p))))::subst1), (uu____19329))))
end)))
end)) uu____19071 sub_pats1 simple_bvs1))
in (match (uu____19049) with
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

let uu___388_19541 = hd1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e1))); FStar_Syntax_Syntax.p = uu___388_19541.FStar_Syntax_Syntax.p})
in (

let uu____19546 = (aux simple_pats1 bvs1 sub_pats2)
in (((hd2), (b)))::uu____19546)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(match (((bvs1), (sub_pats2))) with
| ((x')::bvs2, ((hd2, uu____19590))::sub_pats3) when (FStar_Syntax_Syntax.bv_eq x x') -> begin
(

let uu____19627 = (aux simple_pats1 bvs2 sub_pats3)
in (((hd2), (b)))::uu____19627)
end
| uu____19647 -> begin
(failwith "Impossible: simple pat variable mismatch")
end)
end
| uu____19673 -> begin
(failwith "Impossible: expected a simple pattern")
end)
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv1, simple_pats) -> begin
(

let nested_pats = (aux simple_pats simple_bvs1 checked_sub_pats)
in (

let uu___389_19716 = pat
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv1), (nested_pats))); FStar_Syntax_Syntax.p = uu___389_19716.FStar_Syntax_Syntax.p}))
end
| uu____19728 -> begin
(failwith "Impossible")
end)))
in (

let uu____19732 = (reconstruct_nested_pat simple_pat_elab)
in ((bvs), (pat_e), (uu____19732), (g)))))
end))
end));
)
end))))
end);
))
in ((

let uu____19736 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Patterns")))
in (match (uu____19736) with
| true -> begin
(

let uu____19741 = (FStar_Syntax_Print.pat_to_string p0)
in (FStar_Util.print1 "Checking pattern: %s\n" uu____19741))
end
| uu____19744 -> begin
()
end));
(

let uu____19746 = (

let uu____19757 = (

let uu___390_19758 = (

let uu____19759 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____19759 FStar_Pervasives_Native.fst))
in {FStar_TypeChecker_Env.solver = uu___390_19758.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___390_19758.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___390_19758.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___390_19758.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___390_19758.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___390_19758.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___390_19758.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___390_19758.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___390_19758.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___390_19758.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___390_19758.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___390_19758.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___390_19758.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___390_19758.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___390_19758.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___390_19758.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___390_19758.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = true; FStar_TypeChecker_Env.is_iface = uu___390_19758.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___390_19758.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___390_19758.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___390_19758.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___390_19758.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___390_19758.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___390_19758.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___390_19758.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___390_19758.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___390_19758.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___390_19758.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___390_19758.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___390_19758.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___390_19758.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___390_19758.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___390_19758.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___390_19758.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___390_19758.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___390_19758.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___390_19758.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___390_19758.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___390_19758.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___390_19758.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___390_19758.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___390_19758.FStar_TypeChecker_Env.nbe})
in (

let uu____19775 = (FStar_TypeChecker_PatternUtils.elaborate_pat env p0)
in (check_nested_pattern uu____19757 uu____19775 pat_t)))
in (match (uu____19746) with
| (bvs, pat_e, pat, g) -> begin
((

let uu____19799 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Patterns")))
in (match (uu____19799) with
| true -> begin
(

let uu____19804 = (FStar_Syntax_Print.pat_to_string pat)
in (

let uu____19806 = (FStar_Syntax_Print.term_to_string pat_e)
in (FStar_Util.print2 "Done checking pattern %s as expression %s\n" uu____19804 uu____19806)))
end
| uu____19809 -> begin
()
end));
(

let uu____19811 = (FStar_TypeChecker_Env.push_bvs env bvs)
in (

let uu____19812 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env pat_e)
in ((pat), (bvs), (uu____19811), (pat_e), (uu____19812), (g))));
)
end));
)))))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp) * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____19858 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____19858) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____19904 = branch1
in (match (uu____19904) with
| (cpat, uu____19946, cbr) -> begin
(

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let uu____19968 = (

let uu____19975 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____19975 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____19968) with
| (scrutinee_env, uu____20009) -> begin
(

let uu____20014 = (tc_pat env pat_t pattern)
in (match (uu____20014) with
| (pattern1, pat_bvs1, pat_env, pat_exp, norm_pat_exp, guard_pat) -> begin
(

let uu____20065 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____20095 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____20095) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_WhenClauseNotSupported), ("When clauses are not yet supported in --verify mode; they will be some day")) e.FStar_Syntax_Syntax.pos)
end
| uu____20116 -> begin
(

let uu____20118 = (

let uu____20125 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_Syntax_Util.t_bool)
in (tc_term uu____20125 e))
in (match (uu____20118) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____20065) with
| (when_clause1, g_when) -> begin
(

let uu____20179 = (tc_term pat_env branch_exp)
in (match (uu____20179) with
| (branch_exp1, c, g_branch) -> begin
((FStar_TypeChecker_Env.def_check_guard_wf cbr.FStar_Syntax_Syntax.pos "tc_eqn.1" pat_env g_branch);
(

let when_condition = (match (when_clause1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____20235 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _0_2 -> FStar_Pervasives_Native.Some (_0_2)) uu____20235))
end)
in (

let uu____20246 = (

let eqs = (

let uu____20268 = (

let uu____20270 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____20270)))
in (match (uu____20268) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20279 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____20286) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____20301) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____20304) -> begin
FStar_Pervasives_Native.None
end
| uu____20307 -> begin
(

let uu____20308 = (

let uu____20311 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____20311 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____20308))
end))
end))
in (

let uu____20314 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch)
in (match (uu____20314) with
| (c1, g_branch1) -> begin
(

let uu____20341 = (match (((eqs), (when_condition))) with
| uu____20358 when (

let uu____20371 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____20371))) -> begin
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

let uu____20402 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____20403 = (FStar_TypeChecker_Env.imp_guard g g_when)
in ((uu____20402), (uu____20403))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____20424 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____20424))
in (

let uu____20425 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____20426 = (

let uu____20427 = (FStar_TypeChecker_Env.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Env.imp_guard uu____20427 g_when))
in ((uu____20425), (uu____20426))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Env.guard_of_guard_formula g_w)
in (

let uu____20445 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____20445), (g_when)))))
end)
in (match (uu____20341) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let maybe_return_c_weak = (fun should_return1 -> (

let c_weak1 = (

let uu____20488 = (should_return1 && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c_weak))
in (match (uu____20488) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env branch_exp1 c_weak)
end
| uu____20491 -> begin
c_weak
end))
in (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak1)))
in (

let uu____20493 = (FStar_TypeChecker_Env.close_guard env binders g_when_weak)
in (

let uu____20494 = (FStar_TypeChecker_Env.conj_guard guard_pat g_branch1)
in ((c_weak.FStar_Syntax_Syntax.eff_name), (c_weak.FStar_Syntax_Syntax.cflags), (maybe_return_c_weak), (uu____20493), (uu____20494))))))
end))
end)))
in (match (uu____20246) with
| (effect_label, cflags, maybe_return_c, g_when1, g_branch1) -> begin
(

let branch_guard = (

let uu____20545 = (

let uu____20547 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____20547)))
in (match (uu____20545) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____20550 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pattern2 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____20601 = (

let uu____20609 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____20609))
in (match (uu____20601) with
| (is_induc, datacons) -> begin
(match (((not (is_induc)) || ((FStar_List.length datacons) > (Prims.parse_int "1")))) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____20625 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____20625) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____20646 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____20662 = (

let uu____20667 = (

let uu____20668 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____20668)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____20667))
in (uu____20662 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____20695 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____20695)::[])))
end)))
end
| uu____20696 -> begin
[]
end)
end)))
in (

let fail1 = (fun uu____20703 -> (

let uu____20704 = (

let uu____20706 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____20708 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____20710 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____20706 uu____20708 uu____20710))))
in (failwith uu____20704)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____20725) -> begin
(head_constructor t1)
end
| uu____20730 -> begin
(fail1 ())
end))
in (

let force_scrutinee = (fun uu____20736 -> (match (scrutinee_tm1) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20737 = (

let uu____20739 = (FStar_Range.string_of_range pattern2.FStar_Syntax_Syntax.p)
in (

let uu____20741 = (FStar_Syntax_Print.pat_to_string pattern2)
in (FStar_Util.format2 "Impossible (%s): scrutinee of match is not defined %s" uu____20739 uu____20741)))
in (failwith uu____20737))
end
| FStar_Pervasives_Native.Some (t) -> begin
t
end))
in (

let pat_exp2 = (

let uu____20748 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____20748 FStar_Syntax_Util.unmeta))
in (match (((pattern2.FStar_Syntax_Syntax.v), (pat_exp2.FStar_Syntax_Syntax.n))) with
| (uu____20753, FStar_Syntax_Syntax.Tm_name (uu____20754)) -> begin
[]
end
| (uu____20755, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| (FStar_Syntax_Syntax.Pat_constant (_c), FStar_Syntax_Syntax.Tm_constant (c1)) -> begin
(

let uu____20758 = (

let uu____20759 = (tc_constant env pat_exp2.FStar_Syntax_Syntax.pos c1)
in (

let uu____20760 = (force_scrutinee ())
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____20759 uu____20760 pat_exp2)))
in (uu____20758)::[])
end
| (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (uu____20761, FStar_Pervasives_Native.Some (uu____20762))), uu____20763) -> begin
(

let uu____20780 = (

let uu____20787 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____20787) with
| (env1, uu____20801) -> begin
(env1.FStar_TypeChecker_Env.type_of env1 pat_exp2)
end))
in (match (uu____20780) with
| (uu____20808, t, uu____20810) -> begin
(

let uu____20811 = (

let uu____20812 = (force_scrutinee ())
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero t uu____20812 pat_exp2))
in (uu____20811)::[])
end))
end
| (FStar_Syntax_Syntax.Pat_cons (uu____20813, []), FStar_Syntax_Syntax.Tm_uinst (uu____20814)) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____20838 = (

let uu____20840 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____20840)))
in (match (uu____20838) with
| true -> begin
(failwith "Impossible: nullary patterns must be data constructors")
end
| uu____20848 -> begin
(

let uu____20850 = (force_scrutinee ())
in (

let uu____20853 = (head_constructor pat_exp2)
in (discriminate uu____20850 uu____20853)))
end)))
end
| (FStar_Syntax_Syntax.Pat_cons (uu____20856, []), FStar_Syntax_Syntax.Tm_fvar (uu____20857)) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____20875 = (

let uu____20877 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____20877)))
in (match (uu____20875) with
| true -> begin
(failwith "Impossible: nullary patterns must be data constructors")
end
| uu____20885 -> begin
(

let uu____20887 = (force_scrutinee ())
in (

let uu____20890 = (head_constructor pat_exp2)
in (discriminate uu____20887 uu____20890)))
end)))
end
| (FStar_Syntax_Syntax.Pat_cons (uu____20893, pat_args), FStar_Syntax_Syntax.Tm_app (head1, args)) -> begin
(

let f = (head_constructor head1)
in (

let uu____20940 = ((

let uu____20944 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____20944))) || (Prims.op_disEquality (FStar_List.length pat_args) (FStar_List.length args)))
in (match (uu____20940) with
| true -> begin
(failwith "Impossible: application patterns must be fully-applied data constructors")
end
| uu____20967 -> begin
(

let sub_term_guards = (

let uu____20972 = (

let uu____20977 = (FStar_List.zip pat_args args)
in (FStar_All.pipe_right uu____20977 (FStar_List.mapi (fun i uu____21063 -> (match (uu____21063) with
| ((pi, uu____21085), (ei, uu____21087)) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let scrutinee_tm2 = (

let uu____21115 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____21115) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| uu____21136 -> begin
(

let proj = (

let uu____21148 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar uu____21148 (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____21150 = (

let uu____21151 = (

let uu____21156 = (

let uu____21157 = (

let uu____21166 = (force_scrutinee ())
in (FStar_Syntax_Syntax.as_arg uu____21166))
in (uu____21157)::[])
in (FStar_Syntax_Syntax.mk_Tm_app proj uu____21156))
in (uu____21151 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in FStar_Pervasives_Native.Some (uu____21150)))
end))
in (build_branch_guard scrutinee_tm2 pi ei)))
end)))))
in (FStar_All.pipe_right uu____20972 FStar_List.flatten))
in (

let uu____21191 = (

let uu____21194 = (force_scrutinee ())
in (discriminate uu____21194 f))
in (FStar_List.append uu____21191 sub_term_guards)))
end)))
end
| (FStar_Syntax_Syntax.Pat_dot_term (uu____21197), uu____21198) -> begin
[]
end
| uu____21205 -> begin
(

let uu____21210 = (

let uu____21212 = (FStar_Syntax_Print.pat_to_string pattern2)
in (

let uu____21214 = (FStar_Syntax_Print.term_to_string pat_exp2)
in (FStar_Util.format2 "Internal error: unexpected elaborated pattern: %s and pattern expression %s" uu____21212 uu____21214)))
in (failwith uu____21210))
end)))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pattern2 pat -> (

let uu____21243 = (

let uu____21245 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____21245)))
in (match (uu____21243) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____21248 -> begin
(

let t = (

let uu____21251 = (build_branch_guard scrutinee_tm1 pattern2 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____21251))
in (

let uu____21260 = (FStar_Syntax_Util.type_u ())
in (match (uu____21260) with
| (k, uu____21266) -> begin
(

let uu____21267 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____21267) with
| (t1, uu____21275, uu____21276) -> begin
t1
end))
end)))
end)))
in (

let branch_guard = (build_and_check_branch_guard (FStar_Pervasives_Native.Some (scrutinee_tm)) pattern1 norm_pat_exp)
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

let uu____21288 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____21288) with
| true -> begin
(

let uu____21291 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____21291))
end
| uu____21295 -> begin
()
end));
(

let uu____21297 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in (

let uu____21314 = (

let uu____21315 = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (FStar_TypeChecker_Util.close_guard_implicits env uu____21315 guard))
in ((uu____21297), (branch_guard), (effect_label), (cflags), (maybe_return_c), (uu____21314))));
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

let uu____21362 = (check_let_bound_def true env1 lb)
in (match (uu____21362) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____21388 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____21410 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____21410), (univ_vars1), (c1)))
end
| uu____21413 -> begin
(

let g11 = (

let uu____21416 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____21416 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let uu____21417 = (

let uu____21430 = (

let uu____21445 = (

let uu____21454 = (

let uu____21461 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____21461)))
in (uu____21454)::[])
in (FStar_TypeChecker_Util.generalize env1 false uu____21445))
in (FStar_List.hd uu____21430))
in (match (uu____21417) with
| (uu____21497, univs1, e11, c11, gvs) -> begin
(

let g12 = (FStar_All.pipe_left (FStar_TypeChecker_Env.map_guard g11) (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env1))
in (

let g13 = (FStar_TypeChecker_Env.abstract_guard_n gvs g12)
in (

let uu____21511 = (FStar_Syntax_Util.lcomp_of_comp c11)
in ((g13), (e11), (univs1), (uu____21511)))))
end)))
end)
in (match (uu____21388) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____21528 = (

let uu____21537 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____21537) with
| true -> begin
(

let uu____21548 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____21548) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____21579 -> begin
((

let uu____21582 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____21582 FStar_TypeChecker_Err.top_level_effect));
(

let uu____21583 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____21583), (c12)));
)
end)
end))
end
| uu____21592 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____21598 = (FStar_Syntax_Syntax.lcomp_comp c11)
in (FStar_All.pipe_right uu____21598 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env1)))
in (

let e21 = (

let uu____21604 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____21604) with
| true -> begin
e2
end
| uu____21609 -> begin
((

let uu____21612 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____21612 FStar_TypeChecker_Err.top_level_effect));
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos);
)
end))
in ((e21), (c))));
)
end))
in (match (uu____21528) with
| (e21, c12) -> begin
((

let uu____21636 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____21636) with
| true -> begin
(

let uu____21639 = (FStar_Syntax_Print.term_to_string e11)
in (FStar_Util.print1 "Let binding BEFORE tcnorm: %s\n" uu____21639))
end
| uu____21642 -> begin
()
end));
(

let e12 = (

let uu____21645 = (FStar_Options.tcnorm ())
in (match (uu____21645) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldAttr ((FStar_Parser_Const.tcnorm_attr)::[]))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env1 e11)
end
| uu____21648 -> begin
e11
end))
in ((

let uu____21651 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____21651) with
| true -> begin
(

let uu____21654 = (FStar_Syntax_Print.term_to_string e12)
in (FStar_Util.print1 "Let binding AFTER tcnorm: %s\n" uu____21654))
end
| uu____21657 -> begin
()
end));
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit)
in (

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e12 lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
in (

let uu____21663 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____21677 = (FStar_Syntax_Util.lcomp_of_comp cres)
in ((uu____21663), (uu____21677), (FStar_TypeChecker_Env.trivial_guard))))));
));
)
end))
end))
end))
end
| uu____21678 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___391_21713 = env1
in {FStar_TypeChecker_Env.solver = uu___391_21713.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___391_21713.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___391_21713.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___391_21713.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___391_21713.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___391_21713.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___391_21713.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___391_21713.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___391_21713.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___391_21713.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___391_21713.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___391_21713.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___391_21713.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___391_21713.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___391_21713.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___391_21713.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___391_21713.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___391_21713.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___391_21713.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___391_21713.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___391_21713.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___391_21713.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___391_21713.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___391_21713.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___391_21713.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___391_21713.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___391_21713.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___391_21713.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___391_21713.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___391_21713.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___391_21713.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___391_21713.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___391_21713.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___391_21713.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___391_21713.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___391_21713.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___391_21713.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___391_21713.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___391_21713.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___391_21713.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___391_21713.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___391_21713.FStar_TypeChecker_Env.nbe})
in (

let uu____21715 = (

let uu____21727 = (

let uu____21728 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____21728 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____21727 lb))
in (match (uu____21715) with
| (e1, uu____21751, c1, g1, annotated) -> begin
(

let pure_or_ghost = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c1)
in (

let is_inline_let = (FStar_Util.for_some (FStar_Syntax_Util.is_fvar FStar_Parser_Const.inline_let_attr) lb.FStar_Syntax_Syntax.lbattrs)
in ((match ((is_inline_let && (not (pure_or_ghost)))) with
| true -> begin
(

let uu____21765 = (

let uu____21771 = (

let uu____21773 = (FStar_Syntax_Print.term_to_string e1)
in (

let uu____21775 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.format2 "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\"" uu____21773 uu____21775)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____21771)))
in (FStar_Errors.raise_error uu____21765 e1.FStar_Syntax_Syntax.pos))
end
| uu____21779 -> begin
()
end);
(

let attrs = (

let uu____21786 = ((pure_or_ghost && (not (is_inline_let))) && (FStar_Syntax_Util.is_unit c1.FStar_Syntax_Syntax.res_typ))
in (match (uu____21786) with
| true -> begin
(FStar_Syntax_Util.inline_let_attr)::lb.FStar_Syntax_Syntax.lbattrs
end
| uu____21795 -> begin
lb.FStar_Syntax_Syntax.lbattrs
end))
in (

let x = (

let uu___392_21798 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___392_21798.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___392_21798.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____21799 = (

let uu____21804 = (

let uu____21805 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____21805)::[])
in (FStar_Syntax_Subst.open_term uu____21804 e2))
in (match (uu____21799) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let env_x = (FStar_TypeChecker_Env.push_bv env2 x1)
in (

let uu____21849 = (tc_term env_x e21)
in (match (uu____21849) with
| (e22, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.maybe_return_e2_and_bind e1.FStar_Syntax_Syntax.pos env2 (FStar_Pervasives_Native.Some (e1)) c1 e22 ((FStar_Pervasives_Native.Some (x1)), (c2)))
in (

let e11 = (FStar_TypeChecker_Util.maybe_lift env2 e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e23 = (FStar_TypeChecker_Util.maybe_lift env2 e22 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let lb1 = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x1)) [] c1.FStar_Syntax_Syntax.res_typ cres.FStar_Syntax_Syntax.eff_name e11 attrs lb.FStar_Syntax_Syntax.lbpos)
in (

let e3 = (

let uu____21874 = (

let uu____21881 = (

let uu____21882 = (

let uu____21896 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____21896)))
in FStar_Syntax_Syntax.Tm_let (uu____21882))
in (FStar_Syntax_Syntax.mk uu____21881))
in (uu____21874 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____21917 = (

let uu____21918 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____21919 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____21918 c1.FStar_Syntax_Syntax.res_typ uu____21919 e11)))
in (FStar_All.pipe_left (fun _0_3 -> FStar_TypeChecker_Common.NonTrivial (_0_3)) uu____21917))
in (

let g21 = (

let uu____21921 = (

let uu____21922 = (FStar_TypeChecker_Env.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Env.imp_guard uu____21922 g2))
in (FStar_TypeChecker_Env.close_guard env2 xb uu____21921))
in (

let g22 = (FStar_TypeChecker_Util.close_guard_implicits env2 xb g21)
in (

let guard = (FStar_TypeChecker_Env.conj_guard g1 g22)
in (

let uu____21925 = (

let uu____21927 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____21927))
in (match (uu____21925) with
| true -> begin
(

let tt = (

let uu____21938 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____21938 FStar_Option.get))
in ((

let uu____21944 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____21944) with
| true -> begin
(

let uu____21949 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____21951 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____21949 uu____21951)))
end
| uu____21954 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____21956 -> begin
(

let uu____21958 = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____21958) with
| (t, g_ex) -> begin
((

let uu____21972 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____21972) with
| true -> begin
(

let uu____21977 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____21979 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____21977 uu____21979)))
end
| uu____21982 -> begin
()
end));
(

let uu____21984 = (FStar_TypeChecker_Env.conj_guard g_ex guard)
in ((e4), ((

let uu___393_21986 = cres
in {FStar_Syntax_Syntax.eff_name = uu___393_21986.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___393_21986.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___393_21986.FStar_Syntax_Syntax.comp_thunk})), (uu____21984)));
)
end))
end))))))))))))
end)))))
end))));
)))
end)))
end
| uu____21987 -> begin
(failwith "Impossible (inner let with more than one lb)")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____22023 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____22023) with
| (lbs1, e21) -> begin
(

let uu____22042 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____22042) with
| (env0, topt) -> begin
(

let uu____22061 = (build_let_rec_env true env0 lbs1)
in (match (uu____22061) with
| (lbs2, rec_env, g_t) -> begin
(

let uu____22084 = (check_let_recs rec_env lbs2)
in (match (uu____22084) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____22104 = (

let uu____22105 = (FStar_TypeChecker_Env.conj_guard g_t g_lbs)
in (FStar_All.pipe_right uu____22105 (FStar_TypeChecker_Rel.solve_deferred_constraints env1)))
in (FStar_All.pipe_right uu____22104 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let all_lb_names = (

let uu____22111 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____22111 (fun _0_4 -> FStar_Pervasives_Native.Some (_0_4))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((Prims.op_Equality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
lb
end
| uu____22145 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)))))
end
| uu____22147 -> begin
(

let ecs = (

let uu____22164 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____22198 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____22198))))))
in (FStar_TypeChecker_Util.generalize env1 true uu____22164))
in (FStar_List.map2 (fun uu____22233 lb -> (match (uu____22233) with
| (x, uvs, e, c, gvs) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)) ecs lbs3))
end)
in (

let cres = (

let uu____22281 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____22281))
in (

let uu____22282 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____22282) with
| (lbs5, e22) -> begin
((

let uu____22302 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____22302 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____22303 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____22303), (cres), (FStar_TypeChecker_Env.trivial_guard)));
)
end))))))
end))
end))
end))
end))
end
| uu____22317 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____22353 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____22353) with
| (lbs1, e21) -> begin
(

let uu____22372 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____22372) with
| (env0, topt) -> begin
(

let uu____22391 = (build_let_rec_env false env0 lbs1)
in (match (uu____22391) with
| (lbs2, rec_env, g_t) -> begin
(

let uu____22414 = (

let uu____22421 = (check_let_recs rec_env lbs2)
in (FStar_All.pipe_right uu____22421 (fun uu____22444 -> (match (uu____22444) with
| (lbs3, g) -> begin
(

let uu____22463 = (FStar_TypeChecker_Env.conj_guard g_t g)
in ((lbs3), (uu____22463)))
end))))
in (match (uu____22414) with
| (lbs3, g_lbs) -> begin
(

let uu____22478 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___394_22501 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___394_22501.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___394_22501.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___395_22503 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___395_22503.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___395_22503.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___395_22503.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___395_22503.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___395_22503.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___395_22503.FStar_Syntax_Syntax.lbpos})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____22478) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____22530 = (tc_term env2 e21)
in (match (uu____22530) with
| (e22, cres, g2) -> begin
(

let cres1 = (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e22 cres)
in (

let cres2 = (FStar_Syntax_Util.lcomp_set_flags cres1 ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
in (

let guard = (

let uu____22549 = (

let uu____22550 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Env.close_guard env2 uu____22550 g2))
in (FStar_TypeChecker_Env.conj_guard g_lbs uu____22549))
in (

let cres3 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres2)
in (

let tres = (norm env2 cres3.FStar_Syntax_Syntax.res_typ)
in (

let cres4 = (

let uu___396_22560 = cres3
in {FStar_Syntax_Syntax.eff_name = uu___396_22560.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___396_22560.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___396_22560.FStar_Syntax_Syntax.comp_thunk})
in (

let guard1 = (

let bs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (

let uu____22568 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____22568)))))
in (FStar_TypeChecker_Util.close_guard_implicits env2 bs guard))
in (

let uu____22569 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____22569) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____22610) -> begin
((e), (cres4), (guard1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____22611 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (match (uu____22611) with
| (tres1, g_ex) -> begin
(

let cres5 = (

let uu___397_22625 = cres4
in {FStar_Syntax_Syntax.eff_name = uu___397_22625.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___397_22625.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___397_22625.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____22626 = (FStar_TypeChecker_Env.conj_guard g_ex guard1)
in ((e), (cres5), (uu____22626))))
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
| uu____22627 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Env.guard_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let uu____22675 = (FStar_Options.ml_ish ())
in (match (uu____22675) with
| true -> begin
false
end
| uu____22680 -> begin
(

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____22683 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____22683) with
| (formals, c) -> begin
(

let uu____22715 = (FStar_Syntax_Util.abs_formals lbdef)
in (match (uu____22715) with
| (actuals, uu____22726, uu____22727) -> begin
(match ((((FStar_List.length formals) < (Prims.parse_int "1")) || ((FStar_List.length actuals) < (Prims.parse_int "1")))) with
| true -> begin
(

let uu____22748 = (

let uu____22754 = (

let uu____22756 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____22758 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____22756 uu____22758)))
in ((FStar_Errors.Fatal_RecursiveFunctionLiteral), (uu____22754)))
in (FStar_Errors.raise_error uu____22748 lbtyp.FStar_Syntax_Syntax.pos))
end
| uu____22763 -> begin
(

let actuals1 = (

let uu____22766 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____22766 actuals))
in ((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____22799 -> begin
(

let uu____22801 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____22801))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____22828 -> begin
(

let uu____22830 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____22830))
end))
in (

let msg = (

let uu____22841 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____22843 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____22841 uu____22843 formals_msg actuals_msg)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_LetRecArgumentMismatch), (msg)) lbdef.FStar_Syntax_Syntax.pos))))
end
| uu____22847 -> begin
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

let uu____22855 = (FStar_List.fold_left (fun uu____22888 lb -> (match (uu____22888) with
| (lbs1, env1, g_acc) -> begin
(

let uu____22913 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____22913) with
| (univ_vars1, t, check_t) -> begin
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univ_vars1)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____22936 = (match ((not (check_t))) with
| true -> begin
((g_acc), (t))
end
| uu____22952 -> begin
(

let env01 = (FStar_TypeChecker_Env.push_univ_vars env0 univ_vars1)
in (

let uu____22955 = (

let uu____22962 = (

let uu____22963 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____22963))
in (tc_check_tot_or_gtot_term (

let uu___398_22974 = env01
in {FStar_TypeChecker_Env.solver = uu___398_22974.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___398_22974.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___398_22974.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___398_22974.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___398_22974.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___398_22974.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___398_22974.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___398_22974.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___398_22974.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___398_22974.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___398_22974.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___398_22974.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___398_22974.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___398_22974.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___398_22974.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___398_22974.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___398_22974.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___398_22974.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___398_22974.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___398_22974.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___398_22974.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___398_22974.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___398_22974.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___398_22974.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___398_22974.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___398_22974.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___398_22974.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___398_22974.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___398_22974.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___398_22974.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___398_22974.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___398_22974.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___398_22974.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___398_22974.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___398_22974.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___398_22974.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___398_22974.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___398_22974.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___398_22974.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___398_22974.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___398_22974.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___398_22974.FStar_TypeChecker_Env.nbe}) t uu____22962))
in (match (uu____22955) with
| (t1, uu____22983, g) -> begin
(

let uu____22985 = (

let uu____22986 = (

let uu____22987 = (FStar_All.pipe_right g (FStar_TypeChecker_Rel.resolve_implicits env2))
in (FStar_All.pipe_right uu____22987 (FStar_TypeChecker_Rel.discharge_guard env2)))
in (FStar_TypeChecker_Env.conj_guard g_acc uu____22986))
in (

let uu____22988 = (norm env01 t1)
in ((uu____22985), (uu____22988))))
end)))
end)
in (match (uu____22936) with
| (g, t1) -> begin
(

let env3 = (

let uu____23008 = (termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1)
in (match (uu____23008) with
| true -> begin
(

let uu___399_23011 = env2
in {FStar_TypeChecker_Env.solver = uu___399_23011.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___399_23011.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___399_23011.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___399_23011.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___399_23011.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___399_23011.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___399_23011.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___399_23011.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___399_23011.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___399_23011.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___399_23011.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___399_23011.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___399_23011.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___399_23011.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1), (univ_vars1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___399_23011.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___399_23011.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___399_23011.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___399_23011.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___399_23011.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___399_23011.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___399_23011.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___399_23011.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___399_23011.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___399_23011.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___399_23011.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___399_23011.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___399_23011.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___399_23011.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___399_23011.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___399_23011.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___399_23011.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___399_23011.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___399_23011.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___399_23011.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___399_23011.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___399_23011.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___399_23011.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___399_23011.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___399_23011.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___399_23011.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___399_23011.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___399_23011.FStar_TypeChecker_Env.nbe})
end
| uu____23018 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname ((univ_vars1), (t1)))
end))
in (

let lb1 = (

let uu___400_23025 = lb
in {FStar_Syntax_Syntax.lbname = uu___400_23025.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___400_23025.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___400_23025.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___400_23025.FStar_Syntax_Syntax.lbpos})
in (((lb1)::lbs1), (env3), (g))))
end))))
end))
end)) (([]), (env), (FStar_TypeChecker_Env.trivial_guard)) lbs)
in (match (uu____22855) with
| (lbs1, env1, g) -> begin
(((FStar_List.rev lbs1)), (env1), (g))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____23051 = (

let uu____23060 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____23086 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____23086) with
| (bs, t, lcomp) -> begin
(match (bs) with
| [] -> begin
(

let uu____23116 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_RecursiveFunctionLiteral), ("Only function literals may be defined recursively")) uu____23116))
end
| uu____23123 -> begin
(

let lb1 = (

let uu___401_23126 = lb
in (

let uu____23127 = (FStar_Syntax_Util.abs bs t lcomp)
in {FStar_Syntax_Syntax.lbname = uu___401_23126.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___401_23126.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___401_23126.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___401_23126.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____23127; FStar_Syntax_Syntax.lbattrs = uu___401_23126.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___401_23126.FStar_Syntax_Syntax.lbpos}))
in (

let uu____23130 = (

let uu____23137 = (FStar_TypeChecker_Env.set_expected_typ env lb1.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____23137 lb1.FStar_Syntax_Syntax.lbdef))
in (match (uu____23130) with
| (e, c, g) -> begin
((

let uu____23146 = (

let uu____23148 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____23148)))
in (match (uu____23146) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedGTotForLetRec), ("Expected let rec to be a Tot term; got effect GTot")) e.FStar_Syntax_Syntax.pos)
end
| uu____23153 -> begin
()
end));
(

let lb2 = (FStar_Syntax_Util.mk_letbinding lb1.FStar_Syntax_Syntax.lbname lb1.FStar_Syntax_Syntax.lbunivs lb1.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e lb1.FStar_Syntax_Syntax.lbattrs lb1.FStar_Syntax_Syntax.lbpos)
in ((lb2), (g)));
)
end)))
end)
end)))))
in (FStar_All.pipe_right uu____23060 FStar_List.unzip))
in (match (uu____23051) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs FStar_TypeChecker_Env.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____23204 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____23204) with
| (env1, uu____23223) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____23231 = (check_lbtyp top_level env lb)
in (match (uu____23231) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (Prims.op_disEquality univ_vars1 []))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UniversePolymorphicInnerLetBound), ("Inner let-bound definitions cannot be universe polymorphic")) e1.FStar_Syntax_Syntax.pos)
end
| uu____23276 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____23280 = (tc_maybe_toplevel_term (

let uu___402_23289 = env11
in {FStar_TypeChecker_Env.solver = uu___402_23289.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___402_23289.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___402_23289.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___402_23289.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___402_23289.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___402_23289.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___402_23289.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___402_23289.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___402_23289.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___402_23289.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___402_23289.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___402_23289.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___402_23289.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___402_23289.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___402_23289.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___402_23289.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___402_23289.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___402_23289.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___402_23289.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___402_23289.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___402_23289.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___402_23289.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___402_23289.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___402_23289.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___402_23289.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___402_23289.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___402_23289.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___402_23289.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___402_23289.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___402_23289.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___402_23289.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___402_23289.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___402_23289.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___402_23289.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___402_23289.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___402_23289.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___402_23289.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___402_23289.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___402_23289.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___402_23289.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___402_23289.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___402_23289.FStar_TypeChecker_Env.nbe}) e11)
in (match (uu____23280) with
| (e12, c1, g1) -> begin
(

let uu____23304 = (

let uu____23309 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____23315 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____23309 e12 c1 wf_annot))
in (match (uu____23304) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Env.conj_guard g1 guard_f)
in ((

let uu____23332 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____23332) with
| true -> begin
(

let uu____23335 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____23337 = (FStar_Syntax_Print.lcomp_to_string c11)
in (

let uu____23339 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked let-bound def %s : %s guard is %s\n" uu____23335 uu____23337 uu____23339))))
end
| uu____23342 -> begin
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

let uu____23378 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____23378) with
| (univ_opening, univ_vars1) -> begin
(

let uu____23411 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in ((FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard), (univ_vars1), (univ_opening), (uu____23411)))
end))
end
| uu____23416 -> begin
(

let uu____23417 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____23417) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____23467 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Env.trivial_guard), (univ_vars1), (univ_opening), (uu____23467)))
end
| uu____23472 -> begin
(

let uu____23474 = (FStar_Syntax_Util.type_u ())
in (match (uu____23474) with
| (k, uu____23494) -> begin
(

let uu____23495 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____23495) with
| (t2, uu____23517, g) -> begin
((

let uu____23520 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____23520) with
| true -> begin
(

let uu____23523 = (

let uu____23525 = (FStar_Syntax_Util.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____23525))
in (

let uu____23526 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____23523 uu____23526)))
end
| uu____23529 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____23532 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____23532))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____23538 -> (match (uu____23538) with
| (x, imp) -> begin
(

let uu____23565 = (FStar_Syntax_Util.type_u ())
in (match (uu____23565) with
| (tu, u) -> begin
((

let uu____23587 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____23587) with
| true -> begin
(

let uu____23590 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____23592 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____23594 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binder %s:%s at type %s\n" uu____23590 uu____23592 uu____23594))))
end
| uu____23597 -> begin
()
end));
(

let uu____23599 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____23599) with
| (t, uu____23621, g) -> begin
(

let uu____23623 = (match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau)) -> begin
(

let uu____23639 = (tc_tactic env tau)
in (match (uu____23639) with
| (tau1, uu____23653, g1) -> begin
((FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau1))), (g1))
end))
end
| uu____23657 -> begin
((imp), (FStar_TypeChecker_Env.trivial_guard))
end)
in (match (uu____23623) with
| (imp1, g') -> begin
(

let x1 = (((

let uu___403_23692 = x
in {FStar_Syntax_Syntax.ppname = uu___403_23692.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___403_23692.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp1))
in ((

let uu____23694 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____23694) with
| true -> begin
(

let uu____23697 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____23701 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____23697 uu____23701)))
end
| uu____23704 -> begin
()
end));
(

let uu____23706 = (push_binding env x1)
in ((x1), (uu____23706), (g), (u)));
))
end))
end));
)
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes) = (fun env bs -> ((

let uu____23718 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____23718) with
| true -> begin
(

let uu____23721 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Checking binders %s\n" uu____23721))
end
| uu____23725 -> begin
()
end));
(

let rec aux = (fun env1 bs1 -> (match (bs1) with
| [] -> begin
(([]), (env1), (FStar_TypeChecker_Env.trivial_guard), ([]))
end
| (b)::bs2 -> begin
(

let uu____23834 = (tc_binder env1 b)
in (match (uu____23834) with
| (b1, env', g, u) -> begin
(

let uu____23883 = (aux env' bs2)
in (match (uu____23883) with
| (bs3, env'1, g', us) -> begin
(

let uu____23944 = (

let uu____23945 = (FStar_TypeChecker_Env.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Env.conj_guard g uu____23945))
in (((b1)::bs3), (env'1), (uu____23944), ((u)::us)))
end))
end))
end))
in (aux env bs));
))
and tc_smt_pats : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____24052 uu____24053 -> (match (((uu____24052), (uu____24053))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____24144 = (tc_term env1 t)
in (match (uu____24144) with
| (t1, uu____24164, g') -> begin
(

let uu____24166 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____24166)))
end))
end)) args (([]), (FStar_TypeChecker_Env.trivial_guard))))
in (FStar_List.fold_right (fun p uu____24220 -> (match (uu____24220) with
| (pats1, g) -> begin
(

let uu____24247 = (tc_args env p)
in (match (uu____24247) with
| (args, g') -> begin
(

let uu____24260 = (FStar_TypeChecker_Env.conj_guard g g')
in (((args)::pats1), (uu____24260)))
end))
end)) pats (([]), (FStar_TypeChecker_Env.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____24273 = (tc_maybe_toplevel_term env e)
in (match (uu____24273) with
| (e1, c, g) -> begin
(

let uu____24289 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____24289) with
| true -> begin
((e1), (c), (g))
end
| uu____24298 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (FStar_Syntax_Syntax.lcomp_comp c)
in (

let c2 = (norm_c env c1)
in (

let uu____24303 = (

let uu____24309 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____24309) with
| true -> begin
(

let uu____24317 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____24317), (false)))
end
| uu____24320 -> begin
(

let uu____24322 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____24322), (true)))
end))
in (match (uu____24303) with
| (target_comp, allow_ghost) -> begin
(

let uu____24335 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____24335) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____24345 = (FStar_Syntax_Util.lcomp_of_comp target_comp)
in (

let uu____24346 = (FStar_TypeChecker_Env.conj_guard g1 g')
in ((e1), (uu____24345), (uu____24346))))
end
| uu____24347 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____24357 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in (FStar_Errors.raise_error uu____24357 e1.FStar_Syntax_Syntax.pos))
end
| uu____24369 -> begin
(

let uu____24371 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in (FStar_Errors.raise_error uu____24371 e1.FStar_Syntax_Syntax.pos))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____24395 = (tc_tot_or_gtot_term env t)
in (match (uu____24395) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____24428 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____24428) with
| true -> begin
(

let uu____24433 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____24433))
end
| uu____24436 -> begin
()
end));
(

let env1 = (

let uu___404_24439 = env
in {FStar_TypeChecker_Env.solver = uu___404_24439.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___404_24439.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___404_24439.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___404_24439.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___404_24439.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___404_24439.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___404_24439.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___404_24439.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___404_24439.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___404_24439.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___404_24439.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___404_24439.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___404_24439.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___404_24439.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___404_24439.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___404_24439.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___404_24439.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___404_24439.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___404_24439.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___404_24439.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___404_24439.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___404_24439.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___404_24439.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___404_24439.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___404_24439.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___404_24439.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___404_24439.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___404_24439.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___404_24439.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___404_24439.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___404_24439.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___404_24439.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___404_24439.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___404_24439.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___404_24439.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___404_24439.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___404_24439.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___404_24439.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___404_24439.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___404_24439.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___404_24439.FStar_TypeChecker_Env.nbe})
in (

let uu____24447 = (FStar_All.try_with (fun uu___406_24461 -> (match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)) (fun uu___405_24473 -> (match (uu___405_24473) with
| FStar_Errors.Error (e1, msg, uu____24482) -> begin
(

let uu____24485 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((e1), (msg)) uu____24485))
end)))
in (match (uu____24447) with
| (t, c, g) -> begin
(

let uu____24502 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____24502) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____24511 -> begin
(

let uu____24513 = (

let uu____24519 = (

let uu____24521 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____24521))
in ((FStar_Errors.Fatal_UnexpectedImplictArgument), (uu____24519)))
in (

let uu____24525 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____24513 uu____24525)))
end))
end)));
))


let level_of_type_fail : 'Auu____24541 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  'Auu____24541 = (fun env e t -> (

let uu____24559 = (

let uu____24565 = (

let uu____24567 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____24567 t))
in ((FStar_Errors.Fatal_UnexpectedTermType), (uu____24565)))
in (

let uu____24571 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____24559 uu____24571))))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____24609 = (

let uu____24610 = (FStar_Syntax_Util.unrefine t1)
in uu____24610.FStar_Syntax_Syntax.n)
in (match (uu____24609) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____24614 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____24618 -> begin
(

let uu____24620 = (FStar_Syntax_Util.type_u ())
in (match (uu____24620) with
| (t_u, u) -> begin
(

let env1 = (

let uu___407_24628 = env
in {FStar_TypeChecker_Env.solver = uu___407_24628.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___407_24628.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___407_24628.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___407_24628.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___407_24628.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___407_24628.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___407_24628.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___407_24628.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___407_24628.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___407_24628.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___407_24628.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___407_24628.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___407_24628.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___407_24628.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___407_24628.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___407_24628.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___407_24628.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___407_24628.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___407_24628.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___407_24628.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___407_24628.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___407_24628.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___407_24628.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___407_24628.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___407_24628.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___407_24628.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___407_24628.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___407_24628.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___407_24628.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___407_24628.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___407_24628.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___407_24628.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___407_24628.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___407_24628.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___407_24628.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___407_24628.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___407_24628.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___407_24628.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___407_24628.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___407_24628.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___407_24628.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___407_24628.FStar_TypeChecker_Env.nbe})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____24633 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____24633))
end
| uu____24635 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____24654 = (

let uu____24655 = (FStar_Syntax_Subst.compress e)
in uu____24655.FStar_Syntax_Syntax.n)
in (match (uu____24654) with
| FStar_Syntax_Syntax.Tm_bvar (uu____24660) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____24667) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____24693) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____24710) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____24757) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____24764 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____24764) with
| ((uu____24775, t), uu____24777) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____24783 = (FStar_Syntax_Util.unfold_lazy i)
in (universe_of_aux env uu____24783))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____24786, (FStar_Util.Inl (t), uu____24788), uu____24789) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____24836, (FStar_Util.Inr (c), uu____24838), uu____24839) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____24887) -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant env e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____24896; FStar_Syntax_Syntax.vars = uu____24897}, us) -> begin
(

let uu____24903 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____24903) with
| ((us', t), uu____24916) -> begin
((match ((Prims.op_disEquality (FStar_List.length us) (FStar_List.length us'))) with
| true -> begin
(

let uu____24923 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), ("Unexpected number of universe instantiations")) uu____24923))
end
| uu____24926 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____24942 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____24944) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____24955) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____24982 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____24982) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____25004 -> (match (uu____25004) with
| (b, uu____25012) -> begin
(

let uu____25017 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____25017))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____25024 = (universe_of_aux env res)
in (level_of_type env res uu____25024)))
in (

let u_c = (FStar_All.pipe_right c1 (FStar_TypeChecker_Util.universe_of_comp env u_res))
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
| FStar_Syntax_Syntax.Tm_bvar (uu____25143) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____25161) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____25201) -> begin
(

let uu____25202 = (universe_of_aux env hd3)
in ((uu____25202), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____25217) -> begin
(

let uu____25218 = (universe_of_aux env hd3)
in ((uu____25218), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____25233) -> begin
(

let uu____25246 = (universe_of_aux env hd3)
in ((uu____25246), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____25261) -> begin
(

let uu____25268 = (universe_of_aux env hd3)
in ((uu____25268), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____25283) -> begin
(

let uu____25310 = (universe_of_aux env hd3)
in ((uu____25310), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____25325) -> begin
(

let uu____25332 = (universe_of_aux env hd3)
in ((uu____25332), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____25347) -> begin
(

let uu____25348 = (universe_of_aux env hd3)
in ((uu____25348), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____25363) -> begin
(

let uu____25378 = (universe_of_aux env hd3)
in ((uu____25378), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____25393) -> begin
(

let uu____25400 = (universe_of_aux env hd3)
in ((uu____25400), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____25415) -> begin
(

let uu____25416 = (universe_of_aux env hd3)
in ((uu____25416), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____25431, (hd4)::uu____25433) -> begin
(

let uu____25498 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____25498) with
| (uu____25515, uu____25516, hd5) -> begin
(

let uu____25534 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____25534) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____25593 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env e)
in (

let uu____25595 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____25595) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____25655 -> begin
(

let uu____25656 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____25656) with
| (env1, uu____25680) -> begin
(

let env2 = (

let uu___408_25686 = env1
in {FStar_TypeChecker_Env.solver = uu___408_25686.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___408_25686.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___408_25686.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___408_25686.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___408_25686.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___408_25686.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___408_25686.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___408_25686.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___408_25686.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___408_25686.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___408_25686.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___408_25686.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___408_25686.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___408_25686.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___408_25686.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___408_25686.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___408_25686.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___408_25686.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___408_25686.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___408_25686.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___408_25686.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___408_25686.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___408_25686.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___408_25686.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___408_25686.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___408_25686.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___408_25686.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___408_25686.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___408_25686.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___408_25686.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___408_25686.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___408_25686.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___408_25686.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___408_25686.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___408_25686.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___408_25686.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___408_25686.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___408_25686.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___408_25686.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___408_25686.FStar_TypeChecker_Env.nbe})
in ((

let uu____25691 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____25691) with
| true -> begin
(

let uu____25696 = (

let uu____25698 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____25698))
in (

let uu____25699 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____25696 uu____25699)))
end
| uu____25702 -> begin
()
end));
(

let uu____25704 = (tc_term env2 hd3)
in (match (uu____25704) with
| (uu____25727, {FStar_Syntax_Syntax.eff_name = uu____25728; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____25730; FStar_Syntax_Syntax.comp_thunk = uu____25731}, g) -> begin
((

let uu____25745 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____25745 (fun a1 -> ())));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____25758 = (type_of_head true hd1 args)
in (match (uu____25758) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env t)
in (

let uu____25805 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____25805) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____25859 -> begin
(

let uu____25861 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____25861))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____25865, (hd1)::uu____25867) -> begin
(

let uu____25932 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____25932) with
| (uu____25935, uu____25936, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____25954, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____26003 = (universe_of_aux env e)
in (level_of_type env e uu____26003)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____26029 = (tc_binders env tps)
in (match (uu____26029) with
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
| FStar_Syntax_Syntax.Tm_delayed (uu____26087) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____26113) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____26119 = (FStar_Syntax_Util.unfold_lazy i)
in (type_of_well_typed_term env uu____26119))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____26121 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env [] fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____26121 (fun uu____26135 -> (match (uu____26135) with
| (t2, uu____26143) -> begin
FStar_Pervasives_Native.Some (t2)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____26145; FStar_Syntax_Syntax.vars = uu____26146}, us) -> begin
(

let uu____26152 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env us fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____26152 (fun uu____26166 -> (match (uu____26166) with
| (t2, uu____26174) -> begin
FStar_Pervasives_Native.Some (t2)
end))))
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____26175)) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(

let uu____26177 = (tc_constant env t1.FStar_Syntax_Syntax.pos sc)
in FStar_Pervasives_Native.Some (uu____26177))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____26179 = (mk_tm_type (FStar_Syntax_Syntax.U_succ (u)))
in FStar_Pervasives_Native.Some (uu____26179))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = eff; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (tbody); FStar_Syntax_Syntax.residual_flags = uu____26184})) -> begin
(

let mk_comp = (

let uu____26228 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____26228) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_Total')
end
| uu____26257 -> begin
(

let uu____26259 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____26259) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_GTotal')
end
| uu____26288 -> begin
FStar_Pervasives_Native.None
end))
end))
in (FStar_Util.bind_opt mk_comp (fun f -> (

let uu____26329 = (universe_of_well_typed_term env tbody)
in (FStar_Util.bind_opt uu____26329 (fun u -> (

let uu____26337 = (

let uu____26340 = (

let uu____26347 = (

let uu____26348 = (

let uu____26363 = (f tbody (FStar_Pervasives_Native.Some (u)))
in ((bs), (uu____26363)))
in FStar_Syntax_Syntax.Tm_arrow (uu____26348))
in (FStar_Syntax_Syntax.mk uu____26347))
in (uu____26340 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
in FStar_Pervasives_Native.Some (uu____26337))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____26403 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____26403) with
| (bs1, c1) -> begin
(

let rec aux = (fun env1 us bs2 -> (match (bs2) with
| [] -> begin
(

let uu____26462 = (universe_of_well_typed_term env1 (FStar_Syntax_Util.comp_result c1))
in (FStar_Util.bind_opt uu____26462 (fun uc -> (

let uu____26470 = (mk_tm_type (FStar_Syntax_Syntax.U_max ((uc)::us)))
in FStar_Pervasives_Native.Some (uu____26470)))))
end
| ((x, imp))::bs3 -> begin
(

let uu____26496 = (universe_of_well_typed_term env1 x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____26496 (fun u_x -> (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x)
in (aux env2 ((u_x)::us) bs3)))))
end))
in (aux env [] bs1))
end))
end
| FStar_Syntax_Syntax.Tm_abs (uu____26505) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____26525) -> begin
(

let uu____26530 = (universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____26530 (fun u_x -> (

let uu____26538 = (mk_tm_type u_x)
in FStar_Pervasives_Native.Some (uu____26538)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____26543; FStar_Syntax_Syntax.vars = uu____26544}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____26623 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____26623) with
| (unary_op1, uu____26643) -> begin
(

let head1 = (

let uu____26671 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____26671))
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (type_of_well_typed_term env t2)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____26719; FStar_Syntax_Syntax.vars = uu____26720}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____26816 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____26816) with
| (unary_op1, uu____26836) -> begin
(

let head1 = (

let uu____26864 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a1)::(a2)::[])))) FStar_Pervasives_Native.None uu____26864))
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (type_of_well_typed_term env t2)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____26920; FStar_Syntax_Syntax.vars = uu____26921}, (uu____26922)::[]) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.t_range)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____26961; FStar_Syntax_Syntax.vars = uu____26962}, ((t2, uu____26964))::(uu____26965)::[]) -> begin
(type_of_well_typed_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let t_hd = (type_of_well_typed_term env hd1)
in (

let rec aux = (fun t_hd1 -> (

let uu____27061 = (

let uu____27062 = (FStar_TypeChecker_Normalize.unfold_whnf env t_hd1)
in uu____27062.FStar_Syntax_Syntax.n)
in (match (uu____27061) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_bs = (FStar_List.length bs)
in (

let bs_t_opt = (match ((n_args < n_bs)) with
| true -> begin
(

let uu____27145 = (FStar_Util.first_N n_args bs)
in (match (uu____27145) with
| (bs1, rest) -> begin
(

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None t_hd1.FStar_Syntax_Syntax.pos)
in (

let uu____27237 = (

let uu____27242 = (FStar_Syntax_Syntax.mk_Total t2)
in (FStar_Syntax_Subst.open_comp bs1 uu____27242))
in (match (uu____27237) with
| (bs2, c1) -> begin
FStar_Pervasives_Native.Some (((bs2), ((FStar_Syntax_Util.comp_result c1))))
end)))
end))
end
| uu____27279 -> begin
(match ((Prims.op_Equality n_args n_bs)) with
| true -> begin
(

let uu____27304 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____27304) with
| (bs1, c1) -> begin
(

let uu____27325 = (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
in (match (uu____27325) with
| true -> begin
FStar_Pervasives_Native.Some (((bs1), ((FStar_Syntax_Util.comp_result c1))))
end
| uu____27362 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| uu____27376 -> begin
FStar_Pervasives_Native.None
end)
end)
in (FStar_Util.bind_opt bs_t_opt (fun uu____27407 -> (match (uu____27407) with
| (bs1, t2) -> begin
(

let subst1 = (FStar_List.map2 (fun b a -> FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), ((FStar_Pervasives_Native.fst a))))) bs1 args)
in (

let uu____27483 = (FStar_Syntax_Subst.subst subst1 t2)
in FStar_Pervasives_Native.Some (uu____27483)))
end))))))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____27485) -> begin
(aux x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____27491, uu____27492) -> begin
(aux t2)
end
| uu____27533 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_Util.bind_opt t_hd aux)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____27534, (FStar_Util.Inl (t2), uu____27536), uu____27537) -> begin
FStar_Pervasives_Native.Some (t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____27584, (FStar_Util.Inr (c), uu____27586), uu____27587) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____27652 = (FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
in FStar_Pervasives_Native.Some (uu____27652))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.t_term)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____27660) -> begin
(type_of_well_typed_term env t2)
end
| FStar_Syntax_Syntax.Tm_match (uu____27665) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____27688) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (uu____27702) -> begin
FStar_Pervasives_Native.None
end))))
and universe_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun env t -> (

let uu____27713 = (type_of_well_typed_term env t)
in (match (uu____27713) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.pos = uu____27719; FStar_Syntax_Syntax.vars = uu____27720}) -> begin
FStar_Pervasives_Native.Some (u)
end
| uu____27723 -> begin
FStar_Pervasives_Native.None
end)))


let check_type_of_well_typed_term' : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun must_total env t k -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let env2 = (

let uu___409_27751 = env1
in {FStar_TypeChecker_Env.solver = uu___409_27751.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___409_27751.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___409_27751.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___409_27751.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___409_27751.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___409_27751.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___409_27751.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___409_27751.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___409_27751.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___409_27751.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___409_27751.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___409_27751.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___409_27751.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___409_27751.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___409_27751.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___409_27751.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___409_27751.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___409_27751.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___409_27751.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___409_27751.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___409_27751.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___409_27751.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___409_27751.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___409_27751.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___409_27751.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___409_27751.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___409_27751.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___409_27751.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___409_27751.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___409_27751.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___409_27751.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___409_27751.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___409_27751.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___409_27751.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___409_27751.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___409_27751.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___409_27751.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___409_27751.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___409_27751.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___409_27751.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___409_27751.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___409_27751.FStar_TypeChecker_Env.nbe})
in (

let slow_check = (fun uu____27758 -> (match (must_total) with
| true -> begin
(

let uu____27760 = (env2.FStar_TypeChecker_Env.type_of env2 t)
in (match (uu____27760) with
| (uu____27767, uu____27768, g) -> begin
g
end))
end
| uu____27770 -> begin
(

let uu____27772 = (env2.FStar_TypeChecker_Env.tc_term env2 t)
in (match (uu____27772) with
| (uu____27779, uu____27780, g) -> begin
g
end))
end))
in (

let uu____27782 = (type_of_well_typed_term env2 t)
in (match (uu____27782) with
| FStar_Pervasives_Native.None -> begin
(slow_check ())
end
| FStar_Pervasives_Native.Some (k') -> begin
((

let uu____27787 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____27787) with
| true -> begin
(

let uu____27792 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____27794 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____27796 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____27798 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n" uu____27792 uu____27794 uu____27796 uu____27798)))))
end
| uu____27801 -> begin
()
end));
(

let g = (FStar_TypeChecker_Rel.subtype_nosmt env2 k' k)
in ((

let uu____27807 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____27807) with
| true -> begin
(

let uu____27812 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____27814 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____27816 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____27818 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n" uu____27812 (match ((FStar_Option.isSome g)) with
| true -> begin
"succeeded with guard"
end
| uu____27824 -> begin
"failed"
end) uu____27814 uu____27816 uu____27818)))))
end
| uu____27827 -> begin
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

let uu___410_27855 = env1
in {FStar_TypeChecker_Env.solver = uu___410_27855.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___410_27855.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___410_27855.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___410_27855.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___410_27855.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___410_27855.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___410_27855.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___410_27855.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___410_27855.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___410_27855.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___410_27855.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___410_27855.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___410_27855.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___410_27855.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___410_27855.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___410_27855.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___410_27855.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___410_27855.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___410_27855.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___410_27855.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___410_27855.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___410_27855.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___410_27855.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___410_27855.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___410_27855.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___410_27855.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___410_27855.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___410_27855.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___410_27855.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___410_27855.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___410_27855.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___410_27855.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___410_27855.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___410_27855.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___410_27855.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___410_27855.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___410_27855.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___410_27855.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___410_27855.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___410_27855.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___410_27855.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___410_27855.FStar_TypeChecker_Env.nbe})
in (

let slow_check = (fun uu____27862 -> (match (must_total) with
| true -> begin
(

let uu____27864 = (env2.FStar_TypeChecker_Env.type_of env2 t)
in (match (uu____27864) with
| (uu____27871, uu____27872, g) -> begin
g
end))
end
| uu____27874 -> begin
(

let uu____27876 = (env2.FStar_TypeChecker_Env.tc_term env2 t)
in (match (uu____27876) with
| (uu____27883, uu____27884, g) -> begin
g
end))
end))
in (

let uu____27886 = (

let uu____27888 = (FStar_Options.__temp_fast_implicits ())
in (FStar_All.pipe_left Prims.op_Negation uu____27888))
in (match (uu____27886) with
| true -> begin
(slow_check ())
end
| uu____27893 -> begin
(check_type_of_well_typed_term' must_total env2 t k)
end))))))




