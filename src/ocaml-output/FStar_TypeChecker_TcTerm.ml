
open Prims
open FStar_Pervasives

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___8_5 = env
in {FStar_TypeChecker_Env.solver = uu___8_5.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___8_5.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___8_5.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___8_5.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___8_5.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___8_5.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___8_5.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___8_5.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___8_5.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___8_5.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___8_5.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___8_5.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___8_5.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___8_5.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___8_5.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___8_5.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___8_5.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___8_5.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___8_5.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___8_5.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___8_5.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___8_5.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___8_5.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___8_5.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___8_5.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___8_5.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___8_5.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___8_5.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___8_5.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___8_5.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___8_5.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___8_5.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___8_5.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___8_5.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___8_5.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___8_5.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___8_5.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___8_5.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___8_5.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___8_5.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___8_5.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___8_5.FStar_TypeChecker_Env.nbe}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___11_13 = env
in {FStar_TypeChecker_Env.solver = uu___11_13.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___11_13.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___11_13.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___11_13.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___11_13.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___11_13.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___11_13.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___11_13.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___11_13.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___11_13.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___11_13.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___11_13.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___11_13.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___11_13.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___11_13.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___11_13.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___11_13.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___11_13.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___11_13.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___11_13.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___11_13.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___11_13.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___11_13.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___11_13.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___11_13.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___11_13.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___11_13.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___11_13.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___11_13.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___11_13.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___11_13.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___11_13.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___11_13.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___11_13.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___11_13.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___11_13.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___11_13.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___11_13.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___11_13.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___11_13.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___11_13.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___11_13.FStar_TypeChecker_Env.nbe}))


let mk_lex_list : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v1 tl1 -> (

let r = (match ((Prims.op_Equality tl1.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
v1.FStar_Syntax_Syntax.pos
end
| uu____47 -> begin
(FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos tl1.FStar_Syntax_Syntax.pos)
end)
in (

let uu____49 = (

let uu____54 = (

let uu____55 = (FStar_Syntax_Syntax.as_arg v1)
in (

let uu____64 = (

let uu____75 = (FStar_Syntax_Syntax.as_arg tl1)
in (uu____75)::[])
in (uu____55)::uu____64))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____54))
in (uu____49 FStar_Pervasives_Native.None r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___0_116 -> (match (uu___0_116) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____121 -> begin
false
end))


let steps : 'Auu____130 . 'Auu____130  ->  FStar_TypeChecker_Env.step Prims.list = (fun env -> (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.NoFullNorm)::[])


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
((t), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____218 -> begin
(

let t1 = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____227 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t1)
in (

let uu____232 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____232) with
| FStar_Pervasives_Native.None -> begin
((t1), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t1)
end
| uu____248 -> begin
(

let fail1 = (fun uu____259 -> (

let msg = (match (head_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____263 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" uu____263))
end
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____267 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____269 = (FStar_TypeChecker_Normalize.term_to_string env head1)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" uu____267 uu____269)))
end)
in (

let uu____272 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_EscapedBoundVar), (msg)) uu____272))))
in (

let uu____278 = (

let uu____291 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____292 = (

let uu____293 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____293))
in (FStar_TypeChecker_Util.new_implicit_var "no escape" uu____291 env uu____292)))
in (match (uu____278) with
| (s, uu____308, g0) -> begin
(

let uu____322 = (FStar_TypeChecker_Rel.try_teq true env t1 s)
in (match (uu____322) with
| FStar_Pervasives_Native.Some (g) -> begin
(

let g1 = (

let uu____332 = (FStar_TypeChecker_Env.conj_guard g g0)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____332))
in ((s), (g1)))
end
| uu____333 -> begin
(fail1 ())
end))
end)))
end)
end))))
end))
in (aux false kt)))


let push_binding : 'Auu____344 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____344)  ->  FStar_TypeChecker_Env.env = (fun env b -> (FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v1 -> (

let uu____399 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____399) with
| true -> begin
s
end
| uu____402 -> begin
(FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), (v1))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags (fun uu____425 -> (

let uu____426 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Util.set_result_typ uu____426 t)))))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> e)


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> ((FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos "value_check_expected_typ" env guard);
(

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____485 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____485))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____488 = (

let uu____495 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____495) with
| FStar_Pervasives_Native.None -> begin
(((memo_tk e t)), (lc), (guard))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____505 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____505) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____519 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____519) with
| (e2, g) -> begin
((

let uu____533 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____533) with
| true -> begin
(

let uu____536 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____538 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____540 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____542 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____536 uu____538 uu____540 uu____542)))))
end
| uu____545 -> begin
()
end));
(

let msg = (

let uu____554 = (FStar_TypeChecker_Env.is_trivial_guard_formula g)
in (match (uu____554) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____567 -> begin
(FStar_All.pipe_left (fun _583 -> FStar_Pervasives_Native.Some (_583)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Env.conj_guard g guard)
in (

let lc2 = (

let uu____586 = ((FStar_All.pipe_right tlc FStar_Util.is_left) && (FStar_TypeChecker_Util.should_return env (FStar_Pervasives_Native.Some (e2)) lc1))
in (match (uu____586) with
| true -> begin
(

let uu____594 = (

let uu____595 = (FStar_TypeChecker_Util.lcomp_univ_opt lc1)
in (FStar_TypeChecker_Util.return_value env uu____595 t1 e2))
in (FStar_All.pipe_right uu____594 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____598 -> begin
lc1
end))
in (

let uu____600 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc2 g1)
in (match (uu____600) with
| (lc3, g2) -> begin
(

let uu____613 = (set_lcomp_result lc3 t')
in (((memo_tk e2 t')), (uu____613), (g2)))
end)))));
)
end)))
end))
end))
in (match (uu____488) with
| (e1, lc1, g) -> begin
((e1), (lc1), (g))
end))));
))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____651 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____651) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____661 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____661) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt ec -> (

let uu____714 = ec
in (match (uu____714) with
| (e, c) -> begin
(

let tot_or_gtot = (fun c1 -> (

let uu____737 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____737) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c1))
end
| uu____740 -> begin
(

let uu____742 = (FStar_Syntax_Util.is_pure_or_ghost_comp c1)
in (match (uu____742) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c1))
end
| uu____745 -> begin
(failwith "Impossible: Expected pure_or_ghost comp")
end))
end)))
in (

let uu____748 = (match (copt) with
| FStar_Pervasives_Native.Some (uu____761) -> begin
((copt), (c))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____764 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Parser_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____767 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____767)))))
in (match (uu____764) with
| true -> begin
(

let uu____776 = (

let uu____779 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____779))
in ((uu____776), (c)))
end
| uu____782 -> begin
(

let uu____784 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____784) with
| true -> begin
(

let uu____793 = (tot_or_gtot c)
in ((FStar_Pervasives_Native.None), (uu____793)))
end
| uu____796 -> begin
(

let uu____798 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____798) with
| true -> begin
(

let uu____807 = (

let uu____810 = (tot_or_gtot c)
in FStar_Pervasives_Native.Some (uu____810))
in ((uu____807), (c)))
end
| uu____813 -> begin
((FStar_Pervasives_Native.None), (c))
end))
end))
end))
end)
in (match (uu____748) with
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

let uu____838 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e uu____838))
in (

let c4 = (FStar_Syntax_Syntax.lcomp_comp c3)
in ((

let uu____841 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Low)
in (match (uu____841) with
| true -> begin
(

let uu____845 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____847 = (FStar_Syntax_Print.comp_to_string c4)
in (

let uu____849 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n" uu____845 uu____847 uu____849))))
end
| uu____852 -> begin
()
end));
(

let uu____854 = (FStar_TypeChecker_Util.check_comp env e c4 expected_c)
in (match (uu____854) with
| (e1, uu____868, g) -> begin
(

let g1 = (

let uu____871 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____871 "could not prove post-condition" g))
in ((

let uu____874 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____874) with
| true -> begin
(

let uu____877 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____879 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect;\n\tguard is: %s\n" uu____877 uu____879)))
end
| uu____882 -> begin
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


let no_logical_guard : 'Auu____894 'Auu____895 . FStar_TypeChecker_Env.env  ->  ('Auu____894 * 'Auu____895 * FStar_TypeChecker_Env.guard_t)  ->  ('Auu____894 * 'Auu____895 * FStar_TypeChecker_Env.guard_t) = (fun env uu____917 -> (match (uu____917) with
| (te, kt, f) -> begin
(

let uu____927 = (FStar_TypeChecker_Env.guard_form f)
in (match (uu____927) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____935 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____941 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____935 uu____941)))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let uu____954 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____954) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "Expected type is None\n")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____959 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____959))
end)))


let rec get_pat_vars' : FStar_Syntax_Syntax.bv Prims.list  ->  Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun all andlist pats -> (

let pats1 = (FStar_Syntax_Util.unmeta pats)
in (

let uu____1001 = (FStar_Syntax_Util.head_and_args pats1)
in (match (uu____1001) with
| (head1, args) -> begin
(

let uu____1046 = (

let uu____1061 = (

let uu____1062 = (FStar_Syntax_Util.un_uinst head1)
in uu____1062.FStar_Syntax_Syntax.n)
in ((uu____1061), (args)))
in (match (uu____1046) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____1078) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
(match (andlist) with
| true -> begin
(FStar_Util.as_set all FStar_Syntax_Syntax.order_bv)
end
| uu____1102 -> begin
(FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____1105, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1106))))::((hd1, FStar_Pervasives_Native.None))::((tl1, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let hdvs = (get_pat_vars' all false hd1)
in (

let tlvs = (get_pat_vars' all andlist tl1)
in (match (andlist) with
| true -> begin
(FStar_Util.set_intersect hdvs tlvs)
end
| uu____1180 -> begin
(FStar_Util.set_union hdvs tlvs)
end)))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____1183, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1184))))::((pat, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
(FStar_Syntax_Free.names pat)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((subpats, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
(get_pat_vars' all true subpats)
end
| uu____1268 -> begin
(FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
end))
end))))
and get_pat_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun all pats -> (get_pat_vars' all false pats))


let check_pat_fvs : 'Auu____1299 . FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * 'Auu____1299) Prims.list  ->  unit = (fun rng env pats bs -> (

let pat_vars = (

let uu____1335 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in (

let uu____1342 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env pats)
in (get_pat_vars uu____1335 uu____1342)))
in (

let uu____1343 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____1370 -> (match (uu____1370) with
| (b, uu____1377) -> begin
(

let uu____1378 = (FStar_Util.set_mem b pat_vars)
in (not (uu____1378)))
end))))
in (match (uu____1343) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____1385) -> begin
(

let uu____1390 = (

let uu____1396 = (

let uu____1398 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____1398))
in ((FStar_Errors.Warning_SMTPatternIllFormed), (uu____1396)))
in (FStar_Errors.log_issue rng uu____1390))
end))))


let check_no_smt_theory_symbols : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun en t -> (

let rec pat_terms = (fun t1 -> (

let t2 = (FStar_Syntax_Util.unmeta t1)
in (

let uu____1424 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____1424) with
| (head1, args) -> begin
(

let uu____1469 = (

let uu____1484 = (

let uu____1485 = (FStar_Syntax_Util.un_uinst head1)
in uu____1485.FStar_Syntax_Syntax.n)
in ((uu____1484), (args)))
in (match (uu____1469) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____1501) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____1523)::((hd1, uu____1525))::((tl1, uu____1527))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____1594 = (pat_terms hd1)
in (

let uu____1597 = (pat_terms tl1)
in (FStar_List.append uu____1594 uu____1597)))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____1601)::((pat, uu____1603))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
(pat)::[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((subpats, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
(pat_terms subpats)
end
| uu____1688 -> begin
[]
end))
end))))
in (

let rec aux = (fun t1 -> (

let uu____1713 = (

let uu____1714 = (FStar_Syntax_Subst.compress t1)
in uu____1714.FStar_Syntax_Syntax.n)
in (match (uu____1713) with
| FStar_Syntax_Syntax.Tm_bvar (uu____1719) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_name (uu____1720) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_type (uu____1721) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1722) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1735) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____1736) -> begin
(t1)::[]
end
| FStar_Syntax_Syntax.Tm_abs (uu____1737) -> begin
(t1)::[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1756) -> begin
(t1)::[]
end
| FStar_Syntax_Syntax.Tm_refine (uu____1771) -> begin
(t1)::[]
end
| FStar_Syntax_Syntax.Tm_match (uu____1778) -> begin
(t1)::[]
end
| FStar_Syntax_Syntax.Tm_let (uu____1801) -> begin
(t1)::[]
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1815) -> begin
(t1)::[]
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1838) -> begin
(t1)::[]
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____1846 = (FStar_TypeChecker_Env.fv_has_attr en fv FStar_Parser_Const.smt_theory_symbol_attr_lid)
in (match (uu____1846) with
| true -> begin
(t1)::[]
end
| uu____1851 -> begin
[]
end))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____1879 = (aux t2)
in (FStar_List.fold_left (fun acc uu____1896 -> (match (uu____1896) with
| (t3, uu____1908) -> begin
(

let uu____1913 = (aux t3)
in (FStar_List.append acc uu____1913))
end)) uu____1879 args))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1917, uu____1918) -> begin
(aux t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1960) -> begin
(aux t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1966) -> begin
(aux t2)
end)))
in (

let tlist = (

let uu____1974 = (FStar_All.pipe_right t pat_terms)
in (FStar_All.pipe_right uu____1974 (FStar_List.collect aux)))
in (match ((Prims.op_Equality (FStar_List.length tlist) (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____1986 -> begin
(

let msg = (FStar_List.fold_left (fun s t1 -> (

let uu____1997 = (

let uu____1999 = (FStar_Syntax_Print.term_to_string t1)
in (Prims.op_Hat " " uu____1999))
in (Prims.op_Hat s uu____1997))) "" tlist)
in (

let uu____2003 = (

let uu____2009 = (FStar_Util.format1 "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s" msg)
in ((FStar_Errors.Warning_SMTPatternIllFormed), (uu____2009)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2003)))
end)))))


let check_smt_pat : 'Auu____2024 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * 'Auu____2024) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  unit = (fun env t bs c -> (

let uu____2065 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____2065) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____2068; FStar_Syntax_Syntax.effect_name = uu____2069; FStar_Syntax_Syntax.result_typ = uu____2070; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____2074))::[]; FStar_Syntax_Syntax.flags = uu____2075}) -> begin
((check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs);
(check_no_smt_theory_symbols env pats);
)
end
| uu____2137 -> begin
(failwith "Impossible")
end)
end
| uu____2139 -> begin
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

let uu___345_2200 = env
in {FStar_TypeChecker_Env.solver = uu___345_2200.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___345_2200.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___345_2200.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___345_2200.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___345_2200.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___345_2200.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___345_2200.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___345_2200.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___345_2200.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___345_2200.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___345_2200.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___345_2200.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___345_2200.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___345_2200.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___345_2200.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___345_2200.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___345_2200.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___345_2200.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___345_2200.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___345_2200.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___345_2200.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___345_2200.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___345_2200.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___345_2200.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___345_2200.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___345_2200.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___345_2200.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___345_2200.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___345_2200.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___345_2200.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___345_2200.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___345_2200.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___345_2200.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___345_2200.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___345_2200.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___345_2200.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___345_2200.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___345_2200.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___345_2200.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___345_2200.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___345_2200.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___345_2200.FStar_TypeChecker_Env.nbe})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> ((

let uu____2226 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____2226) with
| true -> begin
(

let uu____2229 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (

let uu____2232 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "Building a decreases clause over (%s) and %s\n" uu____2229 uu____2232)))
end
| uu____2235 -> begin
()
end));
(

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____2266 -> (match (uu____2266) with
| (b, uu____2276) -> begin
(

let t = (

let uu____2282 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____2282))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____2285) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2286) -> begin
[]
end
| uu____2301 -> begin
(

let uu____2302 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____2302)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____2315 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____2315) with
| (head1, uu____2335) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____2363 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____2371 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___1_2380 -> (match (uu___1_2380) with
| FStar_Syntax_Syntax.DECREASES (uu____2382) -> begin
true
end
| uu____2386 -> begin
false
end))))
in (match (uu____2371) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____2393 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____2414 -> begin
(mk_lex_list xs)
end))
end)))));
))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____2443 -> (match (uu____2443) with
| (l, t, u_names) -> begin
(

let uu____2467 = (

let uu____2468 = (FStar_Syntax_Subst.compress t)
in uu____2468.FStar_Syntax_Syntax.n)
in (match (uu____2467) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____2527 -> (match (uu____2527) with
| (x, imp) -> begin
(

let uu____2546 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____2546) with
| true -> begin
(

let uu____2555 = (

let uu____2556 = (

let uu____2559 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____2559))
in (FStar_Syntax_Syntax.new_bv uu____2556 x.FStar_Syntax_Syntax.sort))
in ((uu____2555), (imp)))
end
| uu____2562 -> begin
((x), (imp))
end))
end))))
in (

let uu____2566 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____2566) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____2587 = (

let uu____2592 = (

let uu____2593 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____2602 = (

let uu____2613 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____2613)::[])
in (uu____2593)::uu____2602))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____2592))
in (uu____2587 FStar_Pervasives_Native.None r))
in (

let precedes2 = (FStar_TypeChecker_Util.label "Could not prove termination of this recursive call" r precedes1)
in (

let uu____2648 = (FStar_Util.prefix formals2)
in (match (uu____2648) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___412_2711 = last1
in (

let uu____2712 = (FStar_Syntax_Util.refine last1 precedes2)
in {FStar_Syntax_Syntax.ppname = uu___412_2711.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___412_2711.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2712}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____2748 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____2748) with
| true -> begin
(

let uu____2751 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____2753 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____2755 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____2751 uu____2753 uu____2755))))
end
| uu____2758 -> begin
()
end));
((l), (t'), (u_names));
))))
end)))))
end)))
end
| uu____2762 -> begin
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

let uu____2826 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1)
in (FStar_TypeChecker_Common.mk_by_tactic tactic uu____2826))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____3439 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____3439) with
| true -> begin
(

let uu____3442 = (

let uu____3444 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3444))
in (

let uu____3446 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____3448 = (

let uu____3450 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____3450))
in (FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____3442 uu____3446 uu____3448))))
end
| uu____3452 -> begin
()
end));
(

let uu____3454 = (FStar_Util.record_time (fun uu____3473 -> (tc_maybe_toplevel_term (

let uu___431_3476 = env
in {FStar_TypeChecker_Env.solver = uu___431_3476.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___431_3476.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___431_3476.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___431_3476.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___431_3476.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___431_3476.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___431_3476.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___431_3476.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___431_3476.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___431_3476.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___431_3476.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___431_3476.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___431_3476.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___431_3476.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___431_3476.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___431_3476.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___431_3476.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___431_3476.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___431_3476.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___431_3476.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___431_3476.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___431_3476.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___431_3476.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___431_3476.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___431_3476.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___431_3476.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___431_3476.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___431_3476.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___431_3476.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___431_3476.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___431_3476.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___431_3476.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___431_3476.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___431_3476.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___431_3476.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___431_3476.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___431_3476.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___431_3476.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___431_3476.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___431_3476.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___431_3476.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___431_3476.FStar_TypeChecker_Env.nbe}) e)))
in (match (uu____3454) with
| (r, ms) -> begin
((

let uu____3501 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____3501) with
| true -> begin
((

let uu____3505 = (

let uu____3507 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3507))
in (

let uu____3509 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____3511 = (

let uu____3513 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____3513))
in (

let uu____3514 = (FStar_Util.string_of_int ms)
in (FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n" uu____3505 uu____3509 uu____3511 uu____3514)))));
(

let uu____3517 = r
in (match (uu____3517) with
| (e1, uu____3525, uu____3526) -> begin
(

let uu____3527 = (

let uu____3529 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3529))
in (

let uu____3531 = (FStar_Syntax_Print.term_to_string e1)
in (

let uu____3533 = (

let uu____3535 = (FStar_Syntax_Subst.compress e1)
in (FStar_Syntax_Print.tag_of_term uu____3535))
in (FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____3527 uu____3531 uu____3533))))
end));
)
end
| uu____3537 -> begin
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
| uu____3549 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in (

let top = (FStar_Syntax_Subst.compress e)
in ((

let uu____3553 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____3553) with
| true -> begin
(

let uu____3556 = (

let uu____3558 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3558))
in (

let uu____3560 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____3562 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3556 uu____3560 uu____3562))))
end
| uu____3565 -> begin
()
end));
(match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3573) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____3603) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3610) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3623) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____3624) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3625) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____3626) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____3627) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3646) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____3661) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____3668) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_quoted (qt, qi) -> begin
(

let projl = (fun uu___2_3684 -> (match (uu___2_3684) with
| FStar_Util.Inl (x) -> begin
x
end
| FStar_Util.Inr (uu____3690) -> begin
(failwith "projl fail")
end))
in (

let non_trivial_antiquotes = (fun qi1 -> (

let is_name1 = (fun t -> (

let uu____3706 = (

let uu____3707 = (FStar_Syntax_Subst.compress t)
in uu____3707.FStar_Syntax_Syntax.n)
in (match (uu____3706) with
| FStar_Syntax_Syntax.Tm_name (uu____3711) -> begin
true
end
| uu____3713 -> begin
false
end)))
in (FStar_Util.for_some (fun uu____3723 -> (match (uu____3723) with
| (uu____3729, t) -> begin
(

let uu____3731 = (is_name1 t)
in (not (uu____3731)))
end)) qi1.FStar_Syntax_Syntax.antiquotes)))
in (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_static when (non_trivial_antiquotes qi) -> begin
(

let e0 = e
in (

let newbvs = (FStar_List.map (fun uu____3750 -> (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_term)) qi.FStar_Syntax_Syntax.antiquotes)
in (

let z = (FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs)
in (

let lbs = (FStar_List.map (fun uu____3793 -> (match (uu____3793) with
| ((bv, t), bv') -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None (FStar_Util.Inl (bv')) [] FStar_Syntax_Syntax.t_term FStar_Parser_Const.effect_Tot_lid t [] t.FStar_Syntax_Syntax.pos)
end)) z)
in (

let qi1 = (

let uu___504_3822 = qi
in (

let uu____3823 = (FStar_List.map (fun uu____3851 -> (match (uu____3851) with
| ((bv, uu____3867), bv') -> begin
(

let uu____3879 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____3879)))
end)) z)
in {FStar_Syntax_Syntax.qkind = uu___504_3822.FStar_Syntax_Syntax.qkind; FStar_Syntax_Syntax.antiquotes = uu____3823}))
in (

let nq = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e1 = (FStar_List.fold_left (fun t lb -> (

let uu____3891 = (

let uu____3898 = (

let uu____3899 = (

let uu____3913 = (

let uu____3916 = (

let uu____3917 = (

let uu____3924 = (projl lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____3924))
in (uu____3917)::[])
in (FStar_Syntax_Subst.close uu____3916 t))
in ((((false), ((lb)::[]))), (uu____3913)))
in FStar_Syntax_Syntax.Tm_let (uu____3899))
in (FStar_Syntax_Syntax.mk uu____3898))
in (uu____3891 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))) nq lbs)
in (tc_maybe_toplevel_term env1 e1))))))))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let aqs = qi.FStar_Syntax_Syntax.antiquotes
in (

let env_tm = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_term)
in (

let uu____3960 = (FStar_List.fold_right (fun uu____3996 uu____3997 -> (match (((uu____3996), (uu____3997))) with
| ((bv, tm), (aqs_rev, guard)) -> begin
(

let uu____4066 = (tc_term env_tm tm)
in (match (uu____4066) with
| (tm1, uu____4084, g) -> begin
(

let uu____4086 = (FStar_TypeChecker_Env.conj_guard g guard)
in (((((bv), (tm1)))::aqs_rev), (uu____4086)))
end))
end)) aqs (([]), (FStar_TypeChecker_Env.trivial_guard)))
in (match (uu____3960) with
| (aqs_rev, guard) -> begin
(

let qi1 = (

let uu___532_4128 = qi
in {FStar_Syntax_Syntax.qkind = uu___532_4128.FStar_Syntax_Syntax.qkind; FStar_Syntax_Syntax.antiquotes = (FStar_List.rev aqs_rev)})
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 tm (FStar_Util.Inl (FStar_Syntax_Syntax.t_term)) guard)))
end))))
end
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let c = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Tac_lid; FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_term; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.SOMETRIVIAL)::(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]})
in (

let uu____4147 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4147) with
| (env', uu____4161) -> begin
(

let uu____4166 = (tc_term (

let uu___541_4175 = env'
in {FStar_TypeChecker_Env.solver = uu___541_4175.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___541_4175.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___541_4175.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___541_4175.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___541_4175.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___541_4175.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___541_4175.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___541_4175.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___541_4175.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___541_4175.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___541_4175.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___541_4175.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___541_4175.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___541_4175.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___541_4175.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___541_4175.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___541_4175.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___541_4175.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___541_4175.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___541_4175.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___541_4175.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___541_4175.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___541_4175.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___541_4175.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___541_4175.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___541_4175.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___541_4175.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___541_4175.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___541_4175.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___541_4175.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___541_4175.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___541_4175.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___541_4175.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___541_4175.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___541_4175.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___541_4175.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___541_4175.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___541_4175.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___541_4175.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___541_4175.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___541_4175.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___541_4175.FStar_TypeChecker_Env.nbe}) qt)
in (match (uu____4166) with
| (qt1, uu____4184, uu____4185) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt1), (qi)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____4191 = (

let uu____4198 = (

let uu____4203 = (FStar_Syntax_Util.lcomp_of_comp c)
in FStar_Util.Inr (uu____4203))
in (value_check_expected_typ env1 top uu____4198 FStar_TypeChecker_Env.trivial_guard))
in (match (uu____4191) with
| (t1, lc, g) -> begin
(

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((t1), (FStar_Syntax_Syntax.Meta_monadic_lift (((FStar_Parser_Const.effect_PURE_lid), (FStar_Parser_Const.effect_TAC_lid), (FStar_Syntax_Syntax.t_term))))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in ((t2), (lc), (g)))
end)))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = uu____4220; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____4221); FStar_Syntax_Syntax.ltyp = uu____4222; FStar_Syntax_Syntax.rng = uu____4223}) -> begin
(

let uu____4234 = (FStar_Syntax_Util.unlazy top)
in (tc_term env1 uu____4234))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(value_check_expected_typ env1 top (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp)) FStar_TypeChecker_Env.trivial_guard)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____4241 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____4241) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___571_4258 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___571_4258.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___571_4258.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___571_4258.FStar_TypeChecker_Env.implicits})
in (

let uu____4259 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____4259), (c), (g1))))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (names1, pats)) -> begin
(

let uu____4301 = (FStar_Syntax_Util.type_u ())
in (match (uu____4301) with
| (t, u) -> begin
(

let uu____4314 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____4314) with
| (e2, c, g) -> begin
(

let uu____4330 = (

let uu____4347 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4347) with
| (env2, uu____4371) -> begin
(tc_smt_pats env2 pats)
end))
in (match (uu____4330) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___594_4409 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___594_4409.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___594_4409.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___594_4409.FStar_TypeChecker_Env.implicits})
in (

let uu____4410 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (((names1), (pats1))))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____4429 = (FStar_TypeChecker_Env.conj_guard g g'1)
in ((uu____4410), (c), (uu____4429)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____4435 = (

let uu____4436 = (FStar_Syntax_Subst.compress e1)
in uu____4436.FStar_Syntax_Syntax.n)
in (match (uu____4435) with
| FStar_Syntax_Syntax.Tm_let ((uu____4445, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____4447; FStar_Syntax_Syntax.lbtyp = uu____4448; FStar_Syntax_Syntax.lbeff = uu____4449; FStar_Syntax_Syntax.lbdef = e11; FStar_Syntax_Syntax.lbattrs = uu____4451; FStar_Syntax_Syntax.lbpos = uu____4452})::[]), e2) -> begin
(

let uu____4483 = (

let uu____4490 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (tc_term uu____4490 e11))
in (match (uu____4483) with
| (e12, c1, g1) -> begin
(

let uu____4500 = (tc_term env1 e2)
in (match (uu____4500) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.maybe_return_e2_and_bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 e21 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let attrs = (

let uu____4524 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____4524) with
| true -> begin
(FStar_Syntax_Util.inline_let_attr)::[]
end
| uu____4529 -> begin
[]
end))
in (

let e3 = (

let uu____4534 = (

let uu____4541 = (

let uu____4542 = (

let uu____4556 = (

let uu____4564 = (

let uu____4567 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_Syntax_Syntax.t_unit), (e13), (attrs), (e13.FStar_Syntax_Syntax.pos)))
in (uu____4567)::[])
in ((false), (uu____4564)))
in ((uu____4556), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____4542))
in (FStar_Syntax_Syntax.mk uu____4541))
in (uu____4534 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____4591 = (FStar_TypeChecker_Env.conj_guard g1 g2)
in ((e5), (c), (uu____4591))))))))))
end))
end))
end
| uu____4592 -> begin
(

let uu____4593 = (tc_term env1 e1)
in (match (uu____4593) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____4615)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic_lift (uu____4627)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____4646 = (tc_term env1 e1)
in (match (uu____4646) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____4670) -> begin
(

let uu____4717 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4717) with
| (env0, uu____4731) -> begin
(

let uu____4736 = (tc_comp env0 expected_c)
in (match (uu____4736) with
| (expected_c1, uu____4750, g) -> begin
(

let uu____4752 = (

let uu____4759 = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result expected_c1) (FStar_TypeChecker_Env.set_expected_typ env0))
in (tc_term uu____4759 e1))
in (match (uu____4752) with
| (e2, c', g') -> begin
(

let uu____4769 = (

let uu____4776 = (

let uu____4781 = (FStar_Syntax_Syntax.lcomp_comp c')
in ((e2), (uu____4781)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____4776))
in (match (uu____4769) with
| (e3, expected_c2, g'') -> begin
(

let uu____4791 = (tc_tactic_opt env0 topt)
in (match (uu____4791) with
| (topt1, gtac) -> begin
(

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inr (expected_c2)), (topt1))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____4851 = (FStar_TypeChecker_Env.conj_guard g' g'')
in (FStar_TypeChecker_Env.conj_guard g uu____4851))
in (

let uu____4852 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____4852) with
| (e5, c, f2) -> begin
(

let final_guard = (

let uu____4869 = (FStar_TypeChecker_Env.conj_guard f f2)
in (wrap_guard_with_tactic_opt topt1 uu____4869))
in (

let uu____4870 = (FStar_TypeChecker_Env.conj_guard final_guard gtac)
in ((e5), (c), (uu____4870))))
end)))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____4874) -> begin
(

let uu____4921 = (FStar_Syntax_Util.type_u ())
in (match (uu____4921) with
| (k, u) -> begin
(

let uu____4934 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____4934) with
| (t1, uu____4948, f) -> begin
(

let uu____4950 = (tc_tactic_opt env1 topt)
in (match (uu____4950) with
| (topt1, gtac) -> begin
(

let uu____4969 = (

let uu____4976 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____4976 e1))
in (match (uu____4969) with
| (e2, c, g) -> begin
(

let uu____4986 = (

let uu____4991 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____4997 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____4991 e2 c f))
in (match (uu____4986) with
| (c1, f1) -> begin
(

let uu____5007 = (

let uu____5014 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (topt1))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____5014 c1))
in (match (uu____5007) with
| (e3, c2, f2) -> begin
(

let final_guard = (

let uu____5061 = (FStar_TypeChecker_Env.conj_guard g f2)
in (FStar_TypeChecker_Env.conj_guard f1 uu____5061))
in (

let final_guard1 = (wrap_guard_with_tactic_opt topt1 final_guard)
in (

let uu____5063 = (FStar_TypeChecker_Env.conj_guard final_guard1 gtac)
in ((e3), (c2), (uu____5063)))))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____5064; FStar_Syntax_Syntax.vars = uu____5065}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____5144 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5144) with
| (unary_op1, uu____5168) -> begin
(

let head1 = (

let uu____5196 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____5196))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____5244; FStar_Syntax_Syntax.vars = uu____5245}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____5324 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5324) with
| (unary_op1, uu____5348) -> begin
(

let head1 = (

let uu____5376 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____5376))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____5424)); FStar_Syntax_Syntax.pos = uu____5425; FStar_Syntax_Syntax.vars = uu____5426}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____5505 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5505) with
| (unary_op1, uu____5529) -> begin
(

let head1 = (

let uu____5557 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____5557))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____5605; FStar_Syntax_Syntax.vars = uu____5606}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____5702 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5702) with
| (unary_op1, uu____5726) -> begin
(

let head1 = (

let uu____5754 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a1)::(a2)::[])))) FStar_Pervasives_Native.None uu____5754))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____5810; FStar_Syntax_Syntax.vars = uu____5811}, ((e1, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____5849 = (

let uu____5856 = (

let uu____5857 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5857))
in (tc_term uu____5856 e1))
in (match (uu____5849) with
| (e2, c, g) -> begin
(

let uu____5881 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5881) with
| (head1, uu____5905) -> begin
(

let uu____5930 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((((e2), (FStar_Pervasives_Native.None)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____5963 = (

let uu____5964 = (

let uu____5965 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_Syntax_Syntax.mk_Total uu____5965))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5964))
in ((uu____5930), (uu____5963), (g))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____5966; FStar_Syntax_Syntax.vars = uu____5967}, ((t, FStar_Pervasives_Native.None))::((r, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____6020 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____6020) with
| (head1, uu____6044) -> begin
(

let env' = (

let uu____6070 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_TypeChecker_Env.set_expected_typ env1 uu____6070))
in (

let uu____6071 = (tc_term env' r)
in (match (uu____6071) with
| (er, uu____6085, gr) -> begin
(

let uu____6087 = (tc_term env1 t)
in (match (uu____6087) with
| (t1, tt, gt1) -> begin
(

let g = (FStar_TypeChecker_Env.conj_guard gr gt1)
in (

let uu____6104 = (

let uu____6105 = (

let uu____6110 = (

let uu____6111 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____6120 = (

let uu____6131 = (FStar_Syntax_Syntax.as_arg r)
in (uu____6131)::[])
in (uu____6111)::uu____6120))
in (FStar_Syntax_Syntax.mk_Tm_app head1 uu____6110))
in (uu____6105 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in ((uu____6104), (tt), (g))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____6164; FStar_Syntax_Syntax.vars = uu____6165}, uu____6166) -> begin
(

let uu____6191 = (

let uu____6197 = (

let uu____6199 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____6199))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____6197)))
in (FStar_Errors.raise_error uu____6191 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____6209; FStar_Syntax_Syntax.vars = uu____6210}, uu____6211) -> begin
(

let uu____6236 = (

let uu____6242 = (

let uu____6244 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____6244))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____6242)))
in (FStar_Errors.raise_error uu____6236 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____6254; FStar_Syntax_Syntax.vars = uu____6255}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify), ("Qualifier on argument to reify is irrelevant and will be ignored")))
end
| uu____6300 -> begin
()
end);
(

let uu____6302 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____6302) with
| (env0, uu____6316) -> begin
(

let uu____6321 = (tc_term env0 e1)
in (match (uu____6321) with
| (e2, c, g) -> begin
(

let uu____6337 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____6337) with
| (reify_op, uu____6361) -> begin
(

let u_c = (env1.FStar_TypeChecker_Env.universe_of env1 c.FStar_Syntax_Syntax.res_typ)
in (

let ef = (

let uu____6388 = (FStar_Syntax_Syntax.lcomp_comp c)
in (FStar_Syntax_Util.comp_effect_name uu____6388))
in ((

let uu____6392 = (

let uu____6394 = (FStar_TypeChecker_Env.is_user_reifiable_effect env1 ef)
in (not (uu____6394)))
in (match (uu____6392) with
| true -> begin
(

let uu____6397 = (

let uu____6403 = (FStar_Util.format1 "Effect %s cannot be reified" ef.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____6403)))
in (FStar_Errors.raise_error uu____6397 e2.FStar_Syntax_Syntax.pos))
end
| uu____6407 -> begin
()
end));
(

let repr = (

let uu____6410 = (FStar_Syntax_Syntax.lcomp_comp c)
in (FStar_TypeChecker_Env.reify_comp env1 uu____6410 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____6447 = (FStar_TypeChecker_Env.is_total_effect env1 ef)
in (match (uu____6447) with
| true -> begin
(

let uu____6450 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____6450 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____6451 -> begin
(

let ct = {FStar_Syntax_Syntax.comp_univs = (u_c)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Dv_lid; FStar_Syntax_Syntax.result_typ = repr; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = []}
in (

let uu____6462 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_right uu____6462 FStar_Syntax_Util.lcomp_of_comp)))
end))
in (

let uu____6463 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____6463) with
| (e4, c2, g') -> begin
(

let uu____6479 = (FStar_TypeChecker_Env.conj_guard g g')
in ((e4), (c2), (uu____6479)))
end)))));
)))
end))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.pos = uu____6481; FStar_Syntax_Syntax.vars = uu____6482}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect), ("Qualifier on argument to reflect is irrelevant and will be ignored")))
end
| uu____6527 -> begin
()
end);
(

let uu____6530 = (

let uu____6532 = (FStar_TypeChecker_Env.is_user_reifiable_effect env1 l)
in (not (uu____6532)))
in (match (uu____6530) with
| true -> begin
(

let uu____6535 = (

let uu____6541 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____6541)))
in (FStar_Errors.raise_error uu____6535 e1.FStar_Syntax_Syntax.pos))
end
| uu____6545 -> begin
()
end));
(

let uu____6547 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____6547) with
| (reflect_op, uu____6571) -> begin
(

let uu____6596 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____6596) with
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: user reifiable effect has no decl?")
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____6636 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____6636) with
| (env_no_ex, topt) -> begin
(

let uu____6655 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____6675 = (

let uu____6682 = (

let uu____6683 = (

let uu____6700 = (

let uu____6711 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____6720 = (

let uu____6731 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____6731)::[])
in (uu____6711)::uu____6720))
in ((repr), (uu____6700)))
in FStar_Syntax_Syntax.Tm_app (uu____6683))
in (FStar_Syntax_Syntax.mk uu____6682))
in (uu____6675 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____6776 = (

let uu____6783 = (

let uu____6784 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____6784 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____6783 t))
in (match (uu____6776) with
| (t1, uu____6810, g) -> begin
(

let uu____6812 = (

let uu____6813 = (FStar_Syntax_Subst.compress t1)
in uu____6813.FStar_Syntax_Syntax.n)
in (match (uu____6812) with
| FStar_Syntax_Syntax.Tm_app (uu____6826, ((res, uu____6828))::((wp, uu____6830))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____6887 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____6655) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____6913 = (

let uu____6920 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____6920) with
| (e2, c, g) -> begin
((

let uu____6937 = (

let uu____6939 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____6939))
in (match (uu____6937) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 ((((FStar_Errors.Error_UnexpectedGTotComputation), ("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____6960 -> begin
()
end));
(

let uu____6962 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____6962) with
| FStar_Pervasives_Native.None -> begin
((

let uu____6973 = (

let uu____6983 = (

let uu____6991 = (

let uu____6993 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____6995 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____6993 uu____6995)))
in ((FStar_Errors.Error_UnexpectedInstance), (uu____6991), (e2.FStar_Syntax_Syntax.pos)))
in (uu____6983)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____6973));
(

let uu____7013 = (FStar_TypeChecker_Env.conj_guard g g0)
in ((e2), (uu____7013)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____7017 = (

let uu____7018 = (FStar_TypeChecker_Env.conj_guard g g0)
in (FStar_TypeChecker_Env.conj_guard g' uu____7018))
in ((e2), (uu____7017)))
end));
)
end))
in (match (uu____6913) with
| (e2, g) -> begin
(

let c = (

let uu____7034 = (

let uu____7035 = (

let uu____7036 = (

let uu____7037 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____7037)::[])
in (

let uu____7038 = (

let uu____7049 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____7049)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____7036; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____7038; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____7035))
in (FStar_All.pipe_right uu____7034 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____7109 = (comp_check_expected_typ env1 e3 c)
in (match (uu____7109) with
| (e4, c1, g') -> begin
(

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_monadic (((c1.FStar_Syntax_Syntax.eff_name), (c1.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e4.FStar_Syntax_Syntax.pos)
in (

let uu____7132 = (FStar_TypeChecker_Env.conj_guard g' g)
in ((e5), (c1), (uu____7132))))
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

let uu____7171 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____7171) with
| (head2, args) -> begin
(tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, ((uu____7221, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7222))))::((tau, FStar_Pervasives_Native.None))::[]) when ((FStar_Syntax_Util.is_synth_by_tactic head1) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____7275 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____7275) with
| (head2, args) -> begin
(tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) when ((FStar_Syntax_Util.is_synth_by_tactic head1) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____7350 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::rest -> begin
(((((tau), (FStar_Pervasives_Native.None)))::[]), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
(((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b)))))::(((tau), (FStar_Pervasives_Native.None)))::[]), (rest))
end
| uu____7560 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: bad application")) top.FStar_Syntax_Syntax.pos)
end)
in (match (uu____7350) with
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

let uu____7679 = (

let uu____7680 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____7680 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7679 instantiate_both))
in ((

let uu____7696 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____7696) with
| true -> begin
(

let uu____7699 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____7701 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____7703 = (

let uu____7705 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right uu____7705 (fun uu___3_7712 -> (match (uu___3_7712) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) Checking app %s, expected type is %s\n" uu____7699 uu____7701 uu____7703))))
end
| uu____7719 -> begin
()
end));
(

let uu____7721 = (tc_term (no_inst env2) head1)
in (match (uu____7721) with
| (head2, chead, g_head) -> begin
(

let uu____7737 = (

let uu____7744 = (((not (env2.FStar_TypeChecker_Env.lax)) && (

let uu____7747 = (FStar_Options.lax ())
in (not (uu____7747)))) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____7744) with
| true -> begin
(

let uu____7756 = (

let uu____7763 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____7763))
in (match (uu____7756) with
| (e1, c, g) -> begin
((e1), (c), (g))
end))
end
| uu____7775 -> begin
(

let uu____7777 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env2 head2 chead g_head args uu____7777))
end))
in (match (uu____7737) with
| (e1, c, g) -> begin
(

let uu____7789 = (

let uu____7796 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____7796) with
| true -> begin
(

let uu____7805 = (FStar_TypeChecker_Util.maybe_instantiate env0 e1 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____7805) with
| (e2, res_typ, implicits) -> begin
(

let uu____7821 = (FStar_Syntax_Util.set_result_typ_lc c res_typ)
in ((e2), (uu____7821), (implicits)))
end))
end
| uu____7822 -> begin
((e1), (c), (FStar_TypeChecker_Env.trivial_guard))
end))
in (match (uu____7789) with
| (e2, c1, implicits) -> begin
((

let uu____7834 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____7834) with
| true -> begin
(

let uu____7837 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____7837))
end
| uu____7840 -> begin
()
end));
(

let uu____7842 = (comp_check_expected_typ env0 e2 c1)
in (match (uu____7842) with
| (e3, c2, g') -> begin
(

let gres = (FStar_TypeChecker_Env.conj_guard g g')
in (

let gres1 = (FStar_TypeChecker_Env.conj_guard gres implicits)
in ((

let uu____7861 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____7861) with
| true -> begin
(

let uu____7864 = (FStar_Syntax_Print.term_to_string e3)
in (

let uu____7866 = (FStar_TypeChecker_Rel.guard_to_string env2 gres1)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____7864 uu____7866)))
end
| uu____7869 -> begin
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

let uu____7909 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____7909) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____7929 = (tc_term env12 e1)
in (match (uu____7929) with
| (e11, c1, g1) -> begin
(

let uu____7945 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t), (g1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7959 = (FStar_Syntax_Util.type_u ())
in (match (uu____7959) with
| (k, uu____7971) -> begin
(

let uu____7972 = (FStar_TypeChecker_Util.new_implicit_var "match result" e.FStar_Syntax_Syntax.pos env1 k)
in (match (uu____7972) with
| (res_t, uu____7993, g) -> begin
(

let uu____8007 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in (

let uu____8008 = (FStar_TypeChecker_Env.conj_guard g1 g)
in ((uu____8007), (res_t), (uu____8008))))
end))
end))
end)
in (match (uu____7945) with
| (env_branches, res_t, g11) -> begin
((

let uu____8019 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____8019) with
| true -> begin
(

let uu____8022 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____8022))
end
| uu____8025 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____8149 = (

let uu____8154 = (FStar_List.fold_right (fun uu____8236 uu____8237 -> (match (((uu____8236), (uu____8237))) with
| ((branch1, f, eff_label, cflags, c, g), (caccum, gaccum)) -> begin
(

let uu____8482 = (FStar_TypeChecker_Env.conj_guard g gaccum)
in (((((f), (eff_label), (cflags), (c)))::caccum), (uu____8482)))
end)) t_eqns (([]), (FStar_TypeChecker_Env.trivial_guard)))
in (match (uu____8154) with
| (cases, g) -> begin
(

let uu____8587 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____8587), (g)))
end))
in (match (uu____8149) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____8729 -> (match (uu____8729) with
| ((pat, wopt, br), uu____8774, eff_label, uu____8776, uu____8777, uu____8778) -> begin
(

let uu____8815 = (FStar_TypeChecker_Util.maybe_lift env1 br eff_label cres.FStar_Syntax_Syntax.eff_name res_t)
in ((pat), (wopt), (uu____8815)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____8882 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____8882) with
| true -> begin
(mk_match e11)
end
| uu____8885 -> begin
(

let e_match = (

let uu____8890 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____8890))
in (

let lb = (

let uu____8894 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (guard_x)) [] c1.FStar_Syntax_Syntax.res_typ uu____8894 e11 [] e11.FStar_Syntax_Syntax.pos))
in (

let e2 = (

let uu____8900 = (

let uu____8907 = (

let uu____8908 = (

let uu____8922 = (

let uu____8925 = (

let uu____8926 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____8926)::[])
in (FStar_Syntax_Subst.close uu____8925 e_match))
in ((((false), ((lb)::[]))), (uu____8922)))
in FStar_Syntax_Syntax.Tm_let (uu____8908))
in (FStar_Syntax_Syntax.mk uu____8907))
in (uu____8900 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____8959 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____8959) with
| true -> begin
(

let uu____8962 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____8964 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____8962 uu____8964)))
end
| uu____8967 -> begin
()
end));
(

let uu____8969 = (FStar_TypeChecker_Env.conj_guard g11 g_branches)
in ((e2), (cres), (uu____8969)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8970); FStar_Syntax_Syntax.lbunivs = uu____8971; FStar_Syntax_Syntax.lbtyp = uu____8972; FStar_Syntax_Syntax.lbeff = uu____8973; FStar_Syntax_Syntax.lbdef = uu____8974; FStar_Syntax_Syntax.lbattrs = uu____8975; FStar_Syntax_Syntax.lbpos = uu____8976})::[]), uu____8977) -> begin
(check_top_level_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____9003), uu____9004) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____9022); FStar_Syntax_Syntax.lbunivs = uu____9023; FStar_Syntax_Syntax.lbtyp = uu____9024; FStar_Syntax_Syntax.lbeff = uu____9025; FStar_Syntax_Syntax.lbdef = uu____9026; FStar_Syntax_Syntax.lbattrs = uu____9027; FStar_Syntax_Syntax.lbpos = uu____9028})::uu____9029), uu____9030) -> begin
(check_top_level_let_rec env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____9058), uu____9059) -> begin
(check_inner_let_rec env1 top)
end);
))))
and tc_synth : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun head1 env args rng -> (

let uu____9093 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::[] -> begin
((tau), (FStar_Pervasives_Native.None))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9132))))::((tau, FStar_Pervasives_Native.None))::[] -> begin
((tau), (FStar_Pervasives_Native.Some (a)))
end
| uu____9173 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: bad application")) rng)
end)
in (match (uu____9093) with
| (tau, atyp) -> begin
(

let typ = (match (atyp) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____9206 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____9206) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____9210 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: need a type annotation when no expected type is present")) uu____9210))
end))
end)
in (

let uu____9213 = (

let uu____9220 = (

let uu____9221 = (

let uu____9222 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9222))
in (FStar_TypeChecker_Env.set_expected_typ env uu____9221))
in (tc_term uu____9220 typ))
in (match (uu____9213) with
| (typ1, uu____9238, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let uu____9241 = (tc_tactic env tau)
in (match (uu____9241) with
| (tau1, uu____9255, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g2);
(

let t = (env.FStar_TypeChecker_Env.synth_hook env typ1 (

let uu___1191_9260 = tau1
in {FStar_Syntax_Syntax.n = uu___1191_9260.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___1191_9260.FStar_Syntax_Syntax.vars}))
in ((

let uu____9262 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____9262) with
| true -> begin
(

let uu____9267 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____9267))
end
| uu____9270 -> begin
()
end));
(FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(

let uu____9273 = (

let uu____9274 = (FStar_Syntax_Syntax.mk_Total typ1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____9274))
in ((t), (uu____9273), (FStar_TypeChecker_Env.trivial_guard)));
));
)
end));
)
end)))
end)))
and tc_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___1199_9278 = env
in {FStar_TypeChecker_Env.solver = uu___1199_9278.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1199_9278.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1199_9278.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1199_9278.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1199_9278.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1199_9278.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1199_9278.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1199_9278.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1199_9278.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1199_9278.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1199_9278.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1199_9278.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1199_9278.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1199_9278.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1199_9278.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1199_9278.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1199_9278.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1199_9278.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1199_9278.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1199_9278.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___1199_9278.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___1199_9278.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1199_9278.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___1199_9278.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1199_9278.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1199_9278.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1199_9278.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1199_9278.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1199_9278.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1199_9278.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1199_9278.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1199_9278.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1199_9278.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1199_9278.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1199_9278.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1199_9278.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1199_9278.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1199_9278.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1199_9278.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1199_9278.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1199_9278.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1199_9278.FStar_TypeChecker_Env.nbe})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_TypeChecker_Env.guard_t) = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____9301 = (tc_tactic env tactic)
in (match (uu____9301) with
| (tactic1, uu____9315, g) -> begin
((FStar_Pervasives_Native.Some (tactic1)), (g))
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t0 -> (

let uu____9367 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0)
in (match (uu____9367) with
| (e2, t, implicits) -> begin
(

let tc = (

let uu____9388 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____9388) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____9395 -> begin
(

let uu____9397 = (

let uu____9398 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____9398))
in FStar_Util.Inr (uu____9397))
end))
in (

let is_data_ctor = (fun uu___4_9407 -> (match (uu___4_9407) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____9412)) -> begin
true
end
| uu____9420 -> begin
false
end))
in (

let uu____9424 = ((is_data_ctor dc) && (

let uu____9427 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____9427))))
in (match (uu____9424) with
| true -> begin
(

let uu____9436 = (

let uu____9442 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingDataConstructor), (uu____9442)))
in (

let uu____9446 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____9436 uu____9446)))
end
| uu____9453 -> begin
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

let uu____9464 = (

let uu____9466 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____9466))
in (failwith uu____9464))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____9493 = (

let uu____9498 = (FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
in FStar_Util.Inl (uu____9498))
in (value_check_expected_typ env1 e uu____9493 FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____9500 = (

let uu____9513 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____9513) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9528 = (FStar_Syntax_Util.type_u ())
in (match (uu____9528) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Env.trivial_guard))
end))
in (match (uu____9500) with
| (t, uu____9566, g0) -> begin
(

let uu____9580 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____9580) with
| (e1, uu____9601, g1) -> begin
(

let uu____9615 = (

let uu____9616 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____9616 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____9617 = (FStar_TypeChecker_Env.conj_guard g0 g1)
in ((e1), (uu____9615), (uu____9617))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____9619 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____9629 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____9629)))
end
| uu____9630 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____9619) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___1264_9643 = x
in {FStar_Syntax_Syntax.ppname = uu___1264_9643.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1264_9643.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Env.insert_bv_info env1 x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____9646 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____9646) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____9667 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____9667) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____9674 -> begin
(

let uu____9676 = (

let uu____9677 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____9677))
in FStar_Util.Inr (uu____9676))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9679; FStar_Syntax_Syntax.vars = uu____9680}, uu____9681) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____9686 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____9686))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____9696 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____9696))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9706; FStar_Syntax_Syntax.vars = uu____9707}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____9716 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9716) with
| ((us', t), range) -> begin
((match ((Prims.op_disEquality (FStar_List.length us1) (FStar_List.length us'))) with
| true -> begin
(

let uu____9740 = (

let uu____9746 = (

let uu____9748 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____9750 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____9752 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____9748 uu____9750 uu____9752))))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____9746)))
in (

let uu____9756 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____9740 uu____9756)))
end
| uu____9757 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____9773 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____9778 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____9778 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____9780 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9780) with
| ((us, t), range) -> begin
((

let uu____9803 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____9803) with
| true -> begin
(

let uu____9808 = (

let uu____9810 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____9810))
in (

let uu____9811 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____9813 = (FStar_Range.string_of_range range)
in (

let uu____9815 = (FStar_Range.string_of_use_range range)
in (

let uu____9817 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____9808 uu____9811 uu____9813 uu____9815 uu____9817))))))
end
| uu____9820 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____9825 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____9825 us))
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

let uu____9853 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____9853) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____9867 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____9867) with
| (env2, uu____9881) -> begin
(

let uu____9886 = (tc_binders env2 bs1)
in (match (uu____9886) with
| (bs2, env3, g, us) -> begin
(

let uu____9905 = (tc_comp env3 c1)
in (match (uu____9905) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___1344_9924 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___1344_9924.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___1344_9924.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____9935 = (FStar_TypeChecker_Env.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Env.conj_guard g uu____9935))
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

let uu____9951 = (

let uu____9956 = (

let uu____9957 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____9957)::[])
in (FStar_Syntax_Subst.open_term uu____9956 phi))
in (match (uu____9951) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____9985 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____9985) with
| (env2, uu____9999) -> begin
(

let uu____10004 = (

let uu____10019 = (FStar_List.hd x1)
in (tc_binder env2 uu____10019))
in (match (uu____10004) with
| (x2, env3, f1, u) -> begin
((

let uu____10055 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____10055) with
| true -> begin
(

let uu____10058 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____10060 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____10062 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____10058 uu____10060 uu____10062))))
end
| uu____10067 -> begin
()
end));
(

let uu____10069 = (FStar_Syntax_Util.type_u ())
in (match (uu____10069) with
| (t_phi, uu____10081) -> begin
(

let uu____10082 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____10082) with
| (phi2, uu____10096, f2) -> begin
(

let e1 = (

let uu___1382_10101 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___1382_10101.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___1382_10101.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____10110 = (FStar_TypeChecker_Env.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Env.conj_guard f1 uu____10110))
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____10138) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____10165 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____10165) with
| true -> begin
(

let uu____10168 = (FStar_Syntax_Print.term_to_string (

let uu___1395_10172 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.pos = uu___1395_10172.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___1395_10172.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____10168))
end
| uu____10186 -> begin
()
end));
(

let uu____10188 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____10188) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____10201 -> begin
(

let uu____10202 = (

let uu____10204 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____10206 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____10204 uu____10206)))
in (failwith uu____10202))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Syntax_Syntax.t_unit
end
| FStar_Const.Const_bool (uu____10218) -> begin
FStar_Syntax_Util.t_bool
end
| FStar_Const.Const_int (uu____10220, FStar_Pervasives_Native.None) -> begin
FStar_Syntax_Syntax.t_int
end
| FStar_Const.Const_int (uu____10233, FStar_Pervasives_Native.Some (msize)) -> begin
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
| FStar_Const.Const_string (uu____10251) -> begin
FStar_Syntax_Syntax.t_string
end
| FStar_Const.Const_real (uu____10257) -> begin
FStar_Syntax_Syntax.t_real
end
| FStar_Const.Const_float (uu____10259) -> begin
FStar_Syntax_Syntax.t_float
end
| FStar_Const.Const_char (uu____10260) -> begin
(

let uu____10262 = (FStar_Syntax_DsEnv.try_lookup_lid env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid)
in (FStar_All.pipe_right uu____10262 FStar_Util.must))
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____10267) -> begin
FStar_Syntax_Syntax.t_range
end
| FStar_Const.Const_range_of -> begin
(

let uu____10268 = (

let uu____10274 = (

let uu____10276 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____10276))
in ((FStar_Errors.Fatal_IllTyped), (uu____10274)))
in (FStar_Errors.raise_error uu____10268 r))
end
| FStar_Const.Const_set_range_of -> begin
(

let uu____10280 = (

let uu____10286 = (

let uu____10288 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____10288))
in ((FStar_Errors.Fatal_IllTyped), (uu____10286)))
in (FStar_Errors.raise_error uu____10280 r))
end
| FStar_Const.Const_reify -> begin
(

let uu____10292 = (

let uu____10298 = (

let uu____10300 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____10300))
in ((FStar_Errors.Fatal_IllTyped), (uu____10298)))
in (FStar_Errors.raise_error uu____10292 r))
end
| FStar_Const.Const_reflect (uu____10304) -> begin
(

let uu____10305 = (

let uu____10311 = (

let uu____10313 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____10313))
in ((FStar_Errors.Fatal_IllTyped), (uu____10311)))
in (FStar_Errors.raise_error uu____10305 r))
end
| uu____10317 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedConstant), ("Unsupported constant")) r)
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____10336) -> begin
(

let uu____10345 = (FStar_Syntax_Util.type_u ())
in (match (uu____10345) with
| (k, u) -> begin
(

let uu____10358 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____10358) with
| (t1, uu____10372, g) -> begin
(

let uu____10374 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____10374), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____10376) -> begin
(

let uu____10385 = (FStar_Syntax_Util.type_u ())
in (match (uu____10385) with
| (k, u) -> begin
(

let uu____10398 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____10398) with
| (t1, uu____10412, g) -> begin
(

let uu____10414 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____10414), (u), (g)))
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

let uu____10424 = (

let uu____10429 = (

let uu____10430 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____10430)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____10429))
in (uu____10424 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____10447 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____10447) with
| (tc1, uu____10461, f) -> begin
(

let uu____10463 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____10463) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____10513 = (

let uu____10514 = (FStar_Syntax_Subst.compress head3)
in uu____10514.FStar_Syntax_Syntax.n)
in (match (uu____10513) with
| FStar_Syntax_Syntax.Tm_uinst (uu____10517, us) -> begin
us
end
| uu____10523 -> begin
[]
end))
in (

let uu____10524 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____10524) with
| (uu____10547, args1) -> begin
(

let uu____10573 = (

let uu____10596 = (FStar_List.hd args1)
in (

let uu____10613 = (FStar_List.tl args1)
in ((uu____10596), (uu____10613))))
in (match (uu____10573) with
| (res, args2) -> begin
(

let uu____10694 = (

let uu____10703 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___5_10731 -> (match (uu___5_10731) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____10739 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____10739) with
| (env1, uu____10751) -> begin
(

let uu____10756 = (tc_tot_or_gtot_term env1 e)
in (match (uu____10756) with
| (e1, uu____10768, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Env.trivial_guard))
end))))
in (FStar_All.pipe_right uu____10703 FStar_List.unzip))
in (match (uu____10694) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___1524_10809 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___1524_10809.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___1524_10809.FStar_Syntax_Syntax.flags}))
in (

let u_c = (FStar_All.pipe_right c2 (FStar_TypeChecker_Util.universe_of_comp env u))
in (

let uu____10815 = (FStar_List.fold_left FStar_TypeChecker_Env.conj_guard f guards)
in ((c2), (u_c), (uu____10815))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____10825) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____10829) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____10839 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____10839))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____10843 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____10843))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(

let uu____10847 = (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x))
in (match (uu____10847) with
| true -> begin
u2
end
| uu____10850 -> begin
(

let uu____10852 = (

let uu____10854 = (

let uu____10856 = (FStar_Syntax_Print.univ_to_string u2)
in (Prims.op_Hat uu____10856 " not found"))
in (Prims.op_Hat "Universe variable " uu____10854))
in (failwith uu____10852))
end))
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____10861 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____10863 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____10863 FStar_Pervasives_Native.snd))
end
| uu____10872 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail1 = (fun msg t -> (

let uu____10903 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in (FStar_Errors.raise_error uu____10903 top.FStar_Syntax_Syntax.pos)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____10992 bs2 bs_expected1 -> (match (uu____10992) with
| (env2, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ([]), (FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((

let special = (fun q1 q2 -> (match (((q1), (q2))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____11183)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____11184))) -> begin
true
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)) -> begin
true
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11199)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____11200))) -> begin
true
end
| uu____11209 -> begin
false
end))
in (

let uu____11219 = ((not ((special imp imp'))) && (

let uu____11222 = (FStar_Syntax_Util.eq_aqual imp imp')
in (Prims.op_disEquality uu____11222 FStar_Syntax_Util.Equal)))
in (match (uu____11219) with
| true -> begin
(

let uu____11224 = (

let uu____11230 = (

let uu____11232 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____11232))
in ((FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation), (uu____11230)))
in (

let uu____11236 = (FStar_Syntax_Syntax.range_of_bv hd1)
in (FStar_Errors.raise_error uu____11224 uu____11236)))
end
| uu____11237 -> begin
()
end)));
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____11240 = (

let uu____11247 = (

let uu____11248 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____11248.FStar_Syntax_Syntax.n)
in (match (uu____11247) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____11259 -> begin
((

let uu____11261 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____11261) with
| true -> begin
(

let uu____11264 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____11264))
end
| uu____11267 -> begin
()
end));
(

let uu____11269 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____11269) with
| (t, uu____11283, g1_env) -> begin
(

let g2_env = (

let uu____11286 = (FStar_TypeChecker_Rel.teq_nosmt_force env2 t expected_t)
in (match (uu____11286) with
| true -> begin
FStar_TypeChecker_Env.trivial_guard
end
| uu____11289 -> begin
(

let uu____11291 = (FStar_TypeChecker_Rel.get_subtyping_prop env2 expected_t t)
in (match (uu____11291) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11294 = (FStar_TypeChecker_Err.basic_type_error env2 FStar_Pervasives_Native.None expected_t t)
in (

let uu____11300 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____11294 uu____11300)))
end
| FStar_Pervasives_Native.Some (g_env) -> begin
(

let uu____11302 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_TypeChecker_Util.label_guard uu____11302 "Type annotation on parameter incompatible with the expected type" g_env))
end))
end))
in (

let uu____11304 = (FStar_TypeChecker_Env.conj_guard g1_env g2_env)
in ((t), (uu____11304))))
end));
)
end))
in (match (uu____11240) with
| (t, g_env) -> begin
(

let hd2 = (

let uu___1622_11330 = hd1
in {FStar_Syntax_Syntax.ppname = uu___1622_11330.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1622_11330.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env_b = (push_binding env2 b)
in (

let subst2 = (

let uu____11353 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____11353))
in (

let uu____11356 = (aux ((env_b), (subst2)) bs3 bs_expected2)
in (match (uu____11356) with
| (env_bs, bs4, rest, g'_env_b, subst3) -> begin
(

let g'_env = (FStar_TypeChecker_Env.close_guard env_bs ((b)::[]) g'_env_b)
in (

let uu____11421 = (FStar_TypeChecker_Env.conj_guard g_env g'_env)
in ((env_bs), ((b)::bs4), (rest), (uu____11421), (subst3))))
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
| uu____11593 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____11603 = (tc_binders env1 bs)
in (match (uu____11603) with
| (bs1, envbody, g_env, uu____11633) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody), (body1), (g_env))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____11689 = (

let uu____11690 = (FStar_Syntax_Subst.compress t2)
in uu____11690.FStar_Syntax_Syntax.n)
in (match (uu____11689) with
| FStar_Syntax_Syntax.Tm_uvar (uu____11723) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____11743 -> begin
(failwith "Impossible")
end);
(

let uu____11753 = (tc_binders env1 bs)
in (match (uu____11753) with
| (bs1, envbody, g_env, uu____11795) -> begin
(

let uu____11796 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____11796) with
| (envbody1, uu____11834) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g_env))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11855); FStar_Syntax_Syntax.pos = uu____11856; FStar_Syntax_Syntax.vars = uu____11857}, uu____11858) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____11902 -> begin
(failwith "Impossible")
end);
(

let uu____11912 = (tc_binders env1 bs)
in (match (uu____11912) with
| (bs1, envbody, g_env, uu____11954) -> begin
(

let uu____11955 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____11955) with
| (envbody1, uu____11993) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g_env))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____12015) -> begin
(

let uu____12020 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____12020) with
| (uu____12081, bs1, bs', copt, env_body, body2, g_env) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), (bs'), (copt), (env_body), (body2), (g_env))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____12158 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____12158) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 body2 -> (

let rec handle_more = (fun uu____12303 c_expected2 body3 -> (match (uu____12303) with
| (env_bs, bs2, more, guard_env, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12417 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env_bs), (bs2), (guard_env), (uu____12417), (body3)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____12434 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____12434))
in (

let uu____12435 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env_bs), (bs2), (guard_env), (uu____12435), (body3))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (

let uu____12452 = ((FStar_Options.ml_ish ()) || (FStar_Syntax_Util.is_named_tot c))
in (match (uu____12452) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env_bs (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____12518 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____12518) with
| (bs_expected4, c_expected4) -> begin
(

let uu____12545 = (check_binders env_bs more_bs bs_expected4)
in (match (uu____12545) with
| (env_bs_bs', bs', more1, guard'_env_bs, subst2) -> begin
(

let guard'_env = (FStar_TypeChecker_Env.close_guard env_bs bs2 guard'_env_bs)
in (

let uu____12600 = (

let uu____12627 = (FStar_TypeChecker_Env.conj_guard guard_env guard'_env)
in ((env_bs_bs'), ((FStar_List.append bs2 bs')), (more1), (uu____12627), (subst2)))
in (handle_more uu____12600 c_expected4 body3)))
end))
end))
end
| uu____12650 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env_bs), (bs2), (guard_env), (c), (body4)))
end))
end
| uu____12664 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env_bs), (bs2), (guard_env), (c), (body4)))
end)))
end)
end))
in (

let uu____12679 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____12679 c_expected1 body2))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___1748_12744 = envbody
in {FStar_TypeChecker_Env.solver = uu___1748_12744.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1748_12744.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1748_12744.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1748_12744.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1748_12744.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1748_12744.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1748_12744.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1748_12744.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1748_12744.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1748_12744.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1748_12744.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1748_12744.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1748_12744.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1748_12744.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___1748_12744.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1748_12744.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1748_12744.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1748_12744.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1748_12744.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___1748_12744.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___1748_12744.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1748_12744.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1748_12744.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1748_12744.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1748_12744.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1748_12744.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1748_12744.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1748_12744.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1748_12744.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1748_12744.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1748_12744.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1748_12744.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1748_12744.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1748_12744.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1748_12744.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1748_12744.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1748_12744.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1748_12744.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1748_12744.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1748_12744.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1748_12744.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1748_12744.FStar_TypeChecker_Env.nbe})
in (

let uu____12751 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____12817 uu____12818 -> (match (((uu____12817), (uu____12818))) with
| ((env2, letrec_binders, g), (l, t3, u_names)) -> begin
(

let uu____12909 = (

let uu____12916 = (

let uu____12917 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____12917 FStar_Pervasives_Native.fst))
in (tc_term uu____12916 t3))
in (match (uu____12909) with
| (t4, uu____12941, g') -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l ((u_names), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____12954 = (FStar_Syntax_Syntax.mk_binder (

let uu___1766_12957 = x
in {FStar_Syntax_Syntax.ppname = uu___1766_12957.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1766_12957.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____12954)::letrec_binders)
end
| uu____12958 -> begin
letrec_binders
end)
in (

let uu____12963 = (FStar_TypeChecker_Env.conj_guard g g')
in ((env3), (lb), (uu____12963)))))
end))
end)) ((envbody1), ([]), (FStar_TypeChecker_Env.trivial_guard))))
in (match (uu____12751) with
| (envbody2, letrec_binders, g) -> begin
(

let uu____12983 = (FStar_TypeChecker_Env.close_guard envbody2 bs1 g)
in ((envbody2), (letrec_binders), (uu____12983)))
end)))))
in (

let uu____12986 = (check_actuals_against_formals env1 bs bs_expected1 body1)
in (match (uu____12986) with
| (envbody, bs1, g_env, c, body2) -> begin
(

let uu____13062 = (mk_letrec_env envbody bs1 c)
in (match (uu____13062) with
| (envbody1, letrecs, g_annots) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in (

let uu____13109 = (FStar_TypeChecker_Env.conj_guard g_env g_annots)
in ((FStar_Pervasives_Native.Some (t2)), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (envbody2), (body2), (uu____13109))))
end))
end))))
end))
end
| uu____13126 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____13158 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____13158))
end
| uu____13160 -> begin
(

let uu____13162 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____13162) with
| (uu____13211, bs1, uu____13213, c_opt, envbody, body2, g_env) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (c_opt), (envbody), (body2), (g_env))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____13245 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____13245) with
| (env1, topt) -> begin
((

let uu____13265 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____13265) with
| true -> begin
(

let uu____13268 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____13268 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____13277 -> begin
"false"
end)))
end
| uu____13280 -> begin
()
end));
(

let uu____13282 = (expected_function_typ1 env1 topt body)
in (match (uu____13282) with
| (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1, g_env) -> begin
((

let uu____13323 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("NYC")))
in (match (uu____13323) with
| true -> begin
(

let uu____13328 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____13331 = (FStar_TypeChecker_Rel.guard_to_string env1 g_env)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n" uu____13328 uu____13331)))
end
| uu____13334 -> begin
()
end));
(

let envbody1 = (FStar_TypeChecker_Env.set_range envbody body1.FStar_Syntax_Syntax.pos)
in (

let uu____13337 = (

let should_check_expected_effect = (

let uu____13350 = (

let uu____13357 = (

let uu____13358 = (FStar_Syntax_Subst.compress body1)
in uu____13358.FStar_Syntax_Syntax.n)
in ((c_opt), (uu____13357)))
in (match (uu____13350) with
| (FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Tm_ascribed (uu____13364, (FStar_Util.Inr (expected_c), uu____13366), uu____13367)) -> begin
false
end
| uu____13417 -> begin
true
end))
in (

let uu____13425 = (tc_term (

let uu___1828_13434 = envbody1
in {FStar_TypeChecker_Env.solver = uu___1828_13434.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1828_13434.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1828_13434.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1828_13434.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1828_13434.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1828_13434.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1828_13434.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1828_13434.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1828_13434.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1828_13434.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1828_13434.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1828_13434.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1828_13434.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1828_13434.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1828_13434.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___1828_13434.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___1828_13434.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1828_13434.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___1828_13434.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___1828_13434.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1828_13434.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1828_13434.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1828_13434.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1828_13434.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1828_13434.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1828_13434.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1828_13434.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1828_13434.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1828_13434.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1828_13434.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1828_13434.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1828_13434.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1828_13434.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1828_13434.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1828_13434.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1828_13434.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1828_13434.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1828_13434.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1828_13434.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1828_13434.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1828_13434.FStar_TypeChecker_Env.nbe}) body1)
in (match (uu____13425) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody1 guard_body)
in (match (should_check_expected_effect) with
| true -> begin
(

let uu____13461 = (

let uu____13468 = (

let uu____13473 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____13473)))
in (check_expected_effect (

let uu___1836_13476 = envbody1
in {FStar_TypeChecker_Env.solver = uu___1836_13476.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1836_13476.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1836_13476.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1836_13476.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1836_13476.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1836_13476.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1836_13476.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1836_13476.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1836_13476.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1836_13476.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1836_13476.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1836_13476.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1836_13476.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1836_13476.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1836_13476.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1836_13476.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1836_13476.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___1836_13476.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1836_13476.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___1836_13476.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___1836_13476.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1836_13476.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1836_13476.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1836_13476.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1836_13476.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1836_13476.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1836_13476.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1836_13476.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1836_13476.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1836_13476.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1836_13476.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1836_13476.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1836_13476.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1836_13476.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1836_13476.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1836_13476.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1836_13476.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1836_13476.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1836_13476.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1836_13476.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1836_13476.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1836_13476.FStar_TypeChecker_Env.nbe}) c_opt uu____13468))
in (match (uu____13461) with
| (body3, cbody1, guard) -> begin
(

let uu____13490 = (FStar_TypeChecker_Env.conj_guard guard_body1 guard)
in ((body3), (cbody1), (uu____13490)))
end))
end
| uu____13495 -> begin
(

let uu____13497 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____13497), (guard_body1)))
end))
end)))
in (match (uu____13337) with
| (body2, cbody, guard_body) -> begin
(

let guard = (

let uu____13522 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____13525 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____13525))))
in (match (uu____13522) with
| true -> begin
(

let uu____13528 = (FStar_TypeChecker_Rel.discharge_guard env1 g_env)
in (

let uu____13529 = (FStar_TypeChecker_Rel.discharge_guard envbody1 guard_body)
in (FStar_TypeChecker_Env.conj_guard uu____13528 uu____13529)))
end
| uu____13530 -> begin
(

let guard = (

let uu____13533 = (FStar_TypeChecker_Env.close_guard env1 (FStar_List.append bs1 letrec_binders) guard_body)
in (FStar_TypeChecker_Env.conj_guard g_env uu____13533))
in guard)
end))
in (

let guard1 = (FStar_TypeChecker_Util.close_guard_implicits env1 bs1 guard)
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody)
in (

let e = (FStar_Syntax_Util.abs bs1 body2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody c_opt)))))
in (

let uu____13547 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____13568) -> begin
((e), (t1), (guard1))
end
| uu____13583 -> begin
(

let uu____13584 = (FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
in (match (uu____13584) with
| (e1, guard') -> begin
(

let uu____13597 = (FStar_TypeChecker_Env.conj_guard guard1 guard')
in ((e1), (t1), (uu____13597)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard1))
end)
in (match (uu____13547) with
| (e1, tfun, guard2) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Total tfun)
in (

let uu____13608 = (

let uu____13613 = (FStar_Syntax_Util.lcomp_of_comp c)
in (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 uu____13613 guard2))
in (match (uu____13608) with
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

let uu____13662 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13662) with
| true -> begin
(

let uu____13665 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____13667 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____13665 uu____13667)))
end
| uu____13670 -> begin
()
end));
(

let monadic_application = (fun uu____13745 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____13745) with
| (head2, chead1, ghead1, cres) -> begin
(

let uu____13806 = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____13806) with
| (rt, g0) -> begin
(

let cres1 = (

let uu___1896_13820 = cres
in {FStar_Syntax_Syntax.eff_name = uu___1896_13820.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___1896_13820.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___1896_13820.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____13821 = (match (bs) with
| [] -> begin
(

let g = (

let uu____13837 = (FStar_TypeChecker_Env.conj_guard ghead1 guard)
in (FStar_All.pipe_left (FStar_TypeChecker_Env.conj_guard g0) uu____13837))
in ((cres1), (g)))
end
| uu____13838 -> begin
(

let g = (

let uu____13848 = (

let uu____13849 = (FStar_TypeChecker_Env.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____13849 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (FStar_TypeChecker_Env.conj_guard g0 uu____13848))
in (

let uu____13850 = (

let uu____13851 = (

let uu____13852 = (

let uu____13853 = (FStar_Syntax_Syntax.lcomp_comp cres1)
in (FStar_Syntax_Util.arrow bs uu____13853))
in (FStar_Syntax_Syntax.mk_Total uu____13852))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____13851))
in ((uu____13850), (g))))
end)
in (match (uu____13821) with
| (cres2, guard1) -> begin
((

let uu____13865 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____13865) with
| true -> begin
(

let uu____13868 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____13868))
end
| uu____13871 -> begin
()
end));
(

let cres3 = (

let head_is_pure_and_some_arg_is_effectful = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1) && (FStar_Util.for_some (fun uu____13888 -> (match (uu____13888) with
| (uu____13898, uu____13899, lc) -> begin
((

let uu____13907 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____13907))) || (FStar_TypeChecker_Util.should_not_inline_lc lc))
end)) arg_comps_rev))
in (

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (

let uu____13920 = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2) && head_is_pure_and_some_arg_is_effectful)
in (match (uu____13920) with
| true -> begin
((

let uu____13924 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13924) with
| true -> begin
(

let uu____13927 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: Return inserted in monadic application: %s\n" uu____13927))
end
| uu____13930 -> begin
()
end));
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2);
)
end
| uu____13932 -> begin
((

let uu____13935 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13935) with
| true -> begin
(

let uu____13938 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: No return inserted in monadic application: %s\n" uu____13938))
end
| uu____13941 -> begin
()
end));
cres2;
)
end))))
in (

let comp = (FStar_List.fold_left (fun out_c uu____13969 -> (match (uu____13969) with
| ((e, q), x, c) -> begin
((

let uu____14011 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14011) with
| true -> begin
(

let uu____14014 = (match (x) with
| FStar_Pervasives_Native.None -> begin
"_"
end
| FStar_Pervasives_Native.Some (x1) -> begin
(FStar_Syntax_Print.bv_to_string x1)
end)
in (

let uu____14019 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____14021 = (FStar_Syntax_Print.lcomp_to_string c)
in (FStar_Util.print3 "(b) Monadic app: Binding argument %s : %s of type (%s)\n" uu____14014 uu____14019 uu____14021))))
end
| uu____14024 -> begin
()
end));
(

let uu____14026 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____14026) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____14031 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end));
)
end)) cres3 arg_comps_rev)
in (

let comp1 = ((

let uu____14037 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14037) with
| true -> begin
(

let uu____14040 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print1 "(c) Monadic app: Binding head %s\n" uu____14040))
end
| uu____14043 -> begin
()
end));
(

let uu____14045 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1)
in (match (uu____14045) with
| true -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (head2)) chead1 ((FStar_Pervasives_Native.None), (comp)))
end
| uu____14050 -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
end));
)
in (

let comp2 = (FStar_TypeChecker_Util.subst_lcomp subst1 comp1)
in (

let shortcuts_evaluation_order = (

let uu____14057 = (

let uu____14058 = (FStar_Syntax_Subst.compress head2)
in uu____14058.FStar_Syntax_Syntax.n)
in (match (uu____14057) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____14063 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____14086 -> (match (uu____14086) with
| (arg, uu____14100, uu____14101) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ))))
end
| uu____14110 -> begin
(

let uu____14112 = (

let map_fun = (fun uu____14178 -> (match (uu____14178) with
| ((e, q), uu____14219, c) -> begin
((

let uu____14242 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14242) with
| true -> begin
(

let uu____14245 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____14247 = (FStar_Syntax_Print.lcomp_to_string c)
in (FStar_Util.print2 "For arg e=(%s) c=(%s)... " uu____14245 uu____14247)))
end
| uu____14250 -> begin
()
end));
(

let uu____14252 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____14252) with
| true -> begin
((

let uu____14278 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14278) with
| true -> begin
(FStar_Util.print_string "... not lifting\n")
end
| uu____14282 -> begin
()
end));
((FStar_Pervasives_Native.None), (((e), (q))));
)
end
| uu____14314 -> begin
(

let warn_effectful_args = ((FStar_TypeChecker_Util.must_erase_for_extraction env chead1.FStar_Syntax_Syntax.res_typ) && (

let uu____14319 = (

let uu____14321 = (

let uu____14322 = (FStar_Syntax_Util.un_uinst head2)
in uu____14322.FStar_Syntax_Syntax.n)
in (match (uu____14321) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____14327 = (FStar_Parser_Const.psconst "ignore")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____14327))
end
| uu____14329 -> begin
true
end))
in (not (uu____14319))))
in ((match (warn_effectful_args) with
| true -> begin
(

let uu____14333 = (

let uu____14339 = (

let uu____14341 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____14343 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format3 "Effectful argument %s (%s) to erased function %s, consider let binding it" uu____14341 c.FStar_Syntax_Syntax.eff_name.FStar_Ident.str uu____14343)))
in ((FStar_Errors.Warning_EffectfulArgumentToErasedFunction), (uu____14339)))
in (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos uu____14333))
end
| uu____14347 -> begin
()
end);
(

let uu____14350 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14350) with
| true -> begin
(FStar_Util.print_string "... lifting!\n")
end
| uu____14354 -> begin
()
end));
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____14358 = (

let uu____14367 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____14367), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____14358)))));
))
end));
)
end))
in (

let uu____14396 = (

let uu____14427 = (

let uu____14456 = (

let uu____14467 = (

let uu____14476 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____14476), (FStar_Pervasives_Native.None), (chead1)))
in (uu____14467)::arg_comps_rev)
in (FStar_List.map map_fun uu____14456))
in (FStar_All.pipe_left FStar_List.split uu____14427))
in (match (uu____14396) with
| (lifted_args, reverse_args) -> begin
(

let uu____14677 = (

let uu____14678 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____14678))
in (

let uu____14699 = (

let uu____14700 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____14700))
in ((lifted_args), (uu____14677), (uu____14699))))
end)))
in (match (uu____14112) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___6_14811 -> (match (uu___6_14811) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1 [] e1.FStar_Syntax_Syntax.pos)
in (

let letbinding = (

let uu____14872 = (

let uu____14879 = (

let uu____14880 = (

let uu____14894 = (

let uu____14897 = (

let uu____14898 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____14898)::[])
in (FStar_Syntax_Subst.close uu____14897 e))
in ((((false), ((lb)::[]))), (uu____14894)))
in FStar_Syntax_Syntax.Tm_let (uu____14880))
in (FStar_Syntax_Syntax.mk uu____14879))
in (uu____14872 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp2.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____14950 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp2 guard1)
in (match (uu____14950) with
| (comp3, g) -> begin
((

let uu____14968 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14968) with
| true -> begin
(

let uu____14971 = (FStar_Syntax_Print.term_to_string app)
in (

let uu____14973 = (FStar_Syntax_Print.lcomp_to_string comp3)
in (FStar_Util.print2 "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n" uu____14971 uu____14973)))
end
| uu____14976 -> begin
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

let rec tc_args = (fun head_info uu____15054 bs args1 -> (match (uu____15054) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____15193))))::rest, ((uu____15195, FStar_Pervasives_Native.None))::uu____15196) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____15257 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (match (uu____15257) with
| (t1, g_ex) -> begin
(

let uu____15270 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____15270) with
| (varg, uu____15291, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____15319 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____15319)))
in (

let guard = (FStar_List.fold_right FStar_TypeChecker_Env.conj_guard ((g_ex)::(g)::[]) implicits)
in (

let uu____15328 = (

let uu____15363 = (

let uu____15374 = (

let uu____15383 = (

let uu____15384 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____15384 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____15383)))
in (uu____15374)::outargs)
in ((subst2), (uu____15363), ((arg)::arg_rets), (guard), (fvs)))
in (tc_args head_info uu____15328 rest args1)))))
end))
end)))
end
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau))))::rest, ((uu____15430, FStar_Pervasives_Native.None))::uu____15431) -> begin
(

let tau1 = (FStar_Syntax_Subst.subst subst1 tau)
in (

let uu____15493 = (tc_tactic env tau1)
in (match (uu____15493) with
| (tau2, uu____15507, g_tau) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____15510 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (match (uu____15510) with
| (t1, g_ex) -> begin
(

let uu____15523 = (

let uu____15536 = (

let uu____15543 = (

let uu____15548 = (FStar_Dyn.mkdyn env)
in ((uu____15548), (tau2)))
in FStar_Pervasives_Native.Some (uu____15543))
in (FStar_TypeChecker_Env.new_implicit_var_aux "Instantiating meta argument in application" head1.FStar_Syntax_Syntax.pos env t1 FStar_Syntax_Syntax.Strict uu____15536))
in (match (uu____15523) with
| (varg, uu____15561, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____15589 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____15589)))
in (

let guard = (FStar_List.fold_right FStar_TypeChecker_Env.conj_guard ((g_ex)::(g)::(g_tau)::[]) implicits)
in (

let uu____15598 = (

let uu____15633 = (

let uu____15644 = (

let uu____15653 = (

let uu____15654 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____15654 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____15653)))
in (uu____15644)::outargs)
in ((subst2), (uu____15633), ((arg)::arg_rets), (guard), (fvs)))
in (tc_args head_info uu____15598 rest args1)))))
end))
end)))
end)))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (uu____15770, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____15771))) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InconsistentImplicitQualifier), ("Inconsistent implicit qualifier; cannot apply meta arguments, just use #")) e.FStar_Syntax_Syntax.pos)
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____15782)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____15783))) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____15791)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____15792))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____15807 -> begin
(

let uu____15816 = (

let uu____15822 = (

let uu____15824 = (FStar_Syntax_Print.aqual_to_string aqual)
in (

let uu____15826 = (FStar_Syntax_Print.aqual_to_string aq)
in (

let uu____15828 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____15830 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format4 "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s" uu____15824 uu____15826 uu____15828 uu____15830)))))
in ((FStar_Errors.Fatal_InconsistentImplicitQualifier), (uu____15822)))
in (FStar_Errors.raise_error uu____15816 e.FStar_Syntax_Syntax.pos))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let aqual1 = (FStar_Syntax_Subst.subst_imp subst1 aqual)
in (

let x1 = (

let uu___2106_15837 = x
in {FStar_Syntax_Syntax.ppname = uu___2106_15837.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2106_15837.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____15839 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____15839) with
| true -> begin
(

let uu____15842 = (FStar_Syntax_Print.bv_to_string x1)
in (

let uu____15844 = (FStar_Syntax_Print.term_to_string x1.FStar_Syntax_Syntax.sort)
in (

let uu____15846 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____15848 = (FStar_Syntax_Print.subst_to_string subst1)
in (

let uu____15850 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print5 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n" uu____15842 uu____15844 uu____15846 uu____15848 uu____15850))))))
end
| uu____15853 -> begin
()
end));
(

let uu____15855 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (match (uu____15855) with
| (targ1, g_ex) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___2115_15870 = env1
in {FStar_TypeChecker_Env.solver = uu___2115_15870.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___2115_15870.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___2115_15870.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___2115_15870.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___2115_15870.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___2115_15870.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___2115_15870.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___2115_15870.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___2115_15870.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___2115_15870.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___2115_15870.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___2115_15870.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___2115_15870.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___2115_15870.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___2115_15870.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___2115_15870.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___2115_15870.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual1); FStar_TypeChecker_Env.is_iface = uu___2115_15870.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___2115_15870.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___2115_15870.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___2115_15870.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___2115_15870.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___2115_15870.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___2115_15870.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___2115_15870.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___2115_15870.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___2115_15870.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___2115_15870.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___2115_15870.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___2115_15870.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___2115_15870.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___2115_15870.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___2115_15870.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___2115_15870.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___2115_15870.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___2115_15870.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___2115_15870.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___2115_15870.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___2115_15870.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___2115_15870.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___2115_15870.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___2115_15870.FStar_TypeChecker_Env.nbe})
in ((

let uu____15872 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____15872) with
| true -> begin
(

let uu____15875 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____15877 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____15879 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____15875 uu____15877 uu____15879))))
end
| uu____15882 -> begin
()
end));
(

let uu____15884 = (tc_term env2 e)
in (match (uu____15884) with
| (e1, c, g_e) -> begin
(

let g1 = (

let uu____15901 = (FStar_TypeChecker_Env.conj_guard g g_e)
in (FStar_All.pipe_left (FStar_TypeChecker_Env.conj_guard g_ex) uu____15901))
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____15924 = (

let uu____15927 = (

let uu____15936 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____15936))
in (FStar_Pervasives_Native.fst uu____15927))
in ((uu____15924), (aq)))
in (

let uu____15945 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____15945) with
| true -> begin
(

let subst2 = (

let uu____15955 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____15955 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____16010 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
)))
end));
))));
)
end
| (uu____16054, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____16090) -> begin
(

let uu____16141 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____16141) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 solve ghead2 tres -> (

let tres1 = (

let uu____16197 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____16197 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____16228 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____16228) with
| (bs2, cres'1) -> begin
(

let head_info1 = (

let uu____16250 = (FStar_Syntax_Util.lcomp_of_comp cres'1)
in ((head2), (chead1), (ghead2), (uu____16250)))
in ((

let uu____16252 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____16252) with
| true -> begin
(FStar_Errors.log_issue tres1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_RedundantExplicitCurrying), ("Potentially redundant explicit currying of a function type")))
end
| uu____16257 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Env.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____16299 when (not (norm1)) -> begin
(

let rec norm_tres = (fun tres2 -> (

let tres3 = (FStar_TypeChecker_Normalize.unfold_whnf env tres2)
in (

let uu____16307 = (

let uu____16308 = (FStar_Syntax_Subst.compress tres3)
in uu____16308.FStar_Syntax_Syntax.n)
in (match (uu____16307) with
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____16311; FStar_Syntax_Syntax.index = uu____16312; FStar_Syntax_Syntax.sort = tres4}, uu____16314) -> begin
(norm_tres tres4)
end
| uu____16322 -> begin
tres3
end))))
in (

let uu____16323 = (norm_tres tres1)
in (aux true solve ghead2 uu____16323)))
end
| uu____16325 when (not (solve)) -> begin
(

let ghead3 = (FStar_TypeChecker_Rel.solve_deferred_constraints env ghead2)
in (aux norm1 true ghead3 tres1))
end
| uu____16328 -> begin
(

let uu____16329 = (

let uu____16335 = (

let uu____16337 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____16339 = (FStar_Util.string_of_int n_args)
in (

let uu____16341 = (FStar_Syntax_Print.term_to_string tres1)
in (FStar_Util.format3 "Too many arguments to function of type %s; got %s arguments, remaining type is %s" uu____16337 uu____16339 uu____16341))))
in ((FStar_Errors.Fatal_ToManyArgumentToFunction), (uu____16335)))
in (

let uu____16345 = (FStar_Syntax_Syntax.argpos arg)
in (FStar_Errors.raise_error uu____16329 uu____16345)))
end)))
in (aux false false ghead1 chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf guard -> (

let uu____16375 = (

let uu____16376 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____16376.FStar_Syntax_Syntax.n)
in (match (uu____16375) with
| FStar_Syntax_Syntax.Tm_uvar (uu____16385) -> begin
(

let uu____16398 = (FStar_List.fold_right (fun uu____16429 uu____16430 -> (match (uu____16430) with
| (bs, guard1) -> begin
(

let uu____16457 = (

let uu____16470 = (

let uu____16471 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____16471 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____16470))
in (match (uu____16457) with
| (t, uu____16488, g) -> begin
(

let uu____16502 = (

let uu____16505 = (FStar_Syntax_Syntax.null_binder t)
in (uu____16505)::bs)
in (

let uu____16506 = (FStar_TypeChecker_Env.conj_guard g guard1)
in ((uu____16502), (uu____16506))))
end))
end)) args (([]), (guard)))
in (match (uu____16398) with
| (bs, guard1) -> begin
(

let uu____16523 = (

let uu____16530 = (

let uu____16543 = (

let uu____16544 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____16544 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____16543))
in (match (uu____16530) with
| (t, uu____16561, g) -> begin
(

let uu____16575 = (FStar_Options.ml_ish ())
in (match (uu____16575) with
| true -> begin
(

let uu____16584 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____16587 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____16584), (uu____16587))))
end
| uu____16590 -> begin
(

let uu____16592 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____16595 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____16592), (uu____16595))))
end))
end))
in (match (uu____16523) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____16614 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____16614) with
| true -> begin
(

let uu____16618 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16620 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____16622 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____16618 uu____16620 uu____16622))))
end
| uu____16625 -> begin
()
end));
(

let g = (

let uu____16628 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____16628))
in (

let uu____16629 = (FStar_TypeChecker_Env.conj_guard g guard2)
in (check_function_app bs_cres uu____16629)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____16630); FStar_Syntax_Syntax.pos = uu____16631; FStar_Syntax_Syntax.vars = uu____16632}, uu____16633) -> begin
(

let uu____16670 = (FStar_List.fold_right (fun uu____16701 uu____16702 -> (match (uu____16702) with
| (bs, guard1) -> begin
(

let uu____16729 = (

let uu____16742 = (

let uu____16743 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____16743 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____16742))
in (match (uu____16729) with
| (t, uu____16760, g) -> begin
(

let uu____16774 = (

let uu____16777 = (FStar_Syntax_Syntax.null_binder t)
in (uu____16777)::bs)
in (

let uu____16778 = (FStar_TypeChecker_Env.conj_guard g guard1)
in ((uu____16774), (uu____16778))))
end))
end)) args (([]), (guard)))
in (match (uu____16670) with
| (bs, guard1) -> begin
(

let uu____16795 = (

let uu____16802 = (

let uu____16815 = (

let uu____16816 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____16816 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____16815))
in (match (uu____16802) with
| (t, uu____16833, g) -> begin
(

let uu____16847 = (FStar_Options.ml_ish ())
in (match (uu____16847) with
| true -> begin
(

let uu____16856 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____16859 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____16856), (uu____16859))))
end
| uu____16862 -> begin
(

let uu____16864 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____16867 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____16864), (uu____16867))))
end))
end))
in (match (uu____16795) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____16886 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____16886) with
| true -> begin
(

let uu____16890 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16892 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____16894 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____16890 uu____16892 uu____16894))))
end
| uu____16897 -> begin
()
end));
(

let g = (

let uu____16900 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____16900))
in (

let uu____16901 = (FStar_TypeChecker_Env.conj_guard g guard2)
in (check_function_app bs_cres uu____16901)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____16924 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____16924) with
| (bs1, c1) -> begin
(

let head_info = (

let uu____16946 = (FStar_Syntax_Util.lcomp_of_comp c1)
in ((head1), (chead), (ghead), (uu____16946)))
in ((

let uu____16948 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____16948) with
| true -> begin
(

let uu____16951 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16953 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____16955 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____16958 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print4 "######tc_args of head %s @ %s with formals=%s and result type=%s\n" uu____16951 uu____16953 uu____16955 uu____16958)))))
end
| uu____16961 -> begin
()
end));
(tc_args head_info (([]), ([]), ([]), (guard), ([])) bs1 args);
))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____17004) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort guard)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____17010, uu____17011) -> begin
(check_function_app t guard)
end
| uu____17052 -> begin
(

let uu____17053 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in (FStar_Errors.raise_error uu____17053 head1.FStar_Syntax_Syntax.pos))
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

let uu____17136 = (FStar_List.fold_left2 (fun uu____17205 uu____17206 uu____17207 -> (match (((uu____17205), (uu____17206), (uu____17207))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((

let uu____17360 = (

let uu____17362 = (FStar_Syntax_Util.eq_aqual aq aq')
in (Prims.op_disEquality uu____17362 FStar_Syntax_Util.Equal))
in (match (uu____17360) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InconsistentImplicitQualifier), ("Inconsistent implicit qualifiers")) e.FStar_Syntax_Syntax.pos)
end
| uu____17366 -> begin
()
end));
(

let uu____17368 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____17368) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____17397 = (FStar_TypeChecker_Env.guard_of_guard_formula short)
in (FStar_TypeChecker_Env.imp_guard uu____17397 g))
in (

let ghost1 = (ghost || ((

let uu____17402 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____17402))) && (

let uu____17405 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____17405)))))
in (

let uu____17407 = (

let uu____17418 = (

let uu____17429 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____17429)::[])
in (FStar_List.append seen uu____17418))
in (

let uu____17462 = (FStar_TypeChecker_Env.conj_guard guard g1)
in ((uu____17407), (uu____17462), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____17136) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____17530 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____17530 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____17531 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____17533 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____17533) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____17550 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_pat : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env pat_t p0 -> (

let fail1 = (fun msg -> (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchedPatternType), (msg)) p0.FStar_Syntax_Syntax.p))
in (

let expected_pat_typ = (fun env1 pos scrutinee_t -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Util.unrefine t)
in (

let uu____17641 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____17641) with
| (head1, args) -> begin
(

let uu____17684 = (

let uu____17685 = (FStar_Syntax_Subst.compress head1)
in uu____17685.FStar_Syntax_Syntax.n)
in (match (uu____17684) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____17689; FStar_Syntax_Syntax.vars = uu____17690}, us) -> begin
(unfold_once t1 f us args)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(unfold_once t1 f [] args)
end
| uu____17697 -> begin
(match (norm1) with
| true -> begin
t1
end
| uu____17699 -> begin
(

let uu____17701 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.Unmeta)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env1 t1)
in (aux true uu____17701))
end)
end))
end))))
and unfold_once = (fun t f us args -> (

let uu____17719 = (FStar_TypeChecker_Env.is_type_constructor env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17719) with
| true -> begin
t
end
| uu____17722 -> begin
(

let uu____17724 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17724) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (head_def_ts) -> begin
(

let uu____17744 = (FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us)
in (match (uu____17744) with
| (uu____17749, head_def) -> begin
(

let t' = (FStar_Syntax_Syntax.mk_Tm_app head_def args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let t'1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::[]) env1 t')
in (aux false t'1)))
end))
end))
end)))
in (

let uu____17756 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::[]) env1 scrutinee_t)
in (aux false uu____17756))))
in (

let pat_typ_ok = (fun env1 pat_t1 scrutinee_t -> ((

let uu____17775 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Patterns")))
in (match (uu____17775) with
| true -> begin
(

let uu____17780 = (FStar_Syntax_Print.term_to_string pat_t1)
in (

let uu____17782 = (FStar_Syntax_Print.term_to_string scrutinee_t)
in (FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n" uu____17780 uu____17782)))
end
| uu____17785 -> begin
()
end));
(

let fail2 = (fun msg -> (

let msg1 = (

let uu____17802 = (FStar_Syntax_Print.term_to_string pat_t1)
in (

let uu____17804 = (FStar_Syntax_Print.term_to_string scrutinee_t)
in (FStar_Util.format3 "Type of pattern (%s) does not match type of scrutinee (%s)%s" uu____17802 uu____17804 msg)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchedPatternType), (msg1)) p0.FStar_Syntax_Syntax.p)))
in (

let uu____17808 = (FStar_Syntax_Util.head_and_args scrutinee_t)
in (match (uu____17808) with
| (head_s, args_s) -> begin
(

let pat_t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 pat_t1)
in (

let uu____17852 = (FStar_Syntax_Util.un_uinst head_s)
in (match (uu____17852) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (uu____17853); FStar_Syntax_Syntax.pos = uu____17854; FStar_Syntax_Syntax.vars = uu____17855} -> begin
(

let uu____17858 = (FStar_Syntax_Util.head_and_args pat_t2)
in (match (uu____17858) with
| (head_p, args_p) -> begin
(

let uu____17901 = (FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p head_s)
in (match (uu____17901) with
| true -> begin
(

let uu____17904 = (

let uu____17905 = (FStar_Syntax_Util.un_uinst head_p)
in uu____17905.FStar_Syntax_Syntax.n)
in (match (uu____17904) with
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
((

let uu____17910 = (

let uu____17912 = (

let uu____17914 = (FStar_Syntax_Syntax.lid_of_fv f)
in (FStar_TypeChecker_Env.is_type_constructor env1 uu____17914))
in (FStar_All.pipe_left Prims.op_Negation uu____17912))
in (match (uu____17910) with
| true -> begin
(fail2 "Pattern matching a non-inductive type")
end
| uu____17919 -> begin
()
end));
(match ((Prims.op_disEquality (FStar_List.length args_p) (FStar_List.length args_s))) with
| true -> begin
(fail2 "")
end
| uu____17940 -> begin
()
end);
(

let uu____17942 = (

let uu____17967 = (

let uu____17971 = (FStar_Syntax_Syntax.lid_of_fv f)
in (FStar_TypeChecker_Env.num_inductive_ty_params env1 uu____17971))
in (match (uu____17967) with
| FStar_Pervasives_Native.None -> begin
((args_p), (args_s))
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____18020 = (FStar_Util.first_N n1 args_p)
in (match (uu____18020) with
| (params_p, uu____18078) -> begin
(

let uu____18119 = (FStar_Util.first_N n1 args_s)
in (match (uu____18119) with
| (params_s, uu____18177) -> begin
((params_p), (params_s))
end))
end))
end))
in (match (uu____17942) with
| (params_p, params_s) -> begin
(FStar_List.fold_left2 (fun out uu____18306 uu____18307 -> (match (((uu____18306), (uu____18307))) with
| ((p, uu____18341), (s, uu____18343)) -> begin
(

let uu____18376 = (FStar_TypeChecker_Rel.teq_nosmt env1 p s)
in (match (uu____18376) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18379 = (

let uu____18381 = (FStar_Syntax_Print.term_to_string p)
in (

let uu____18383 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "; parameter %s <> parameter %s" uu____18381 uu____18383)))
in (fail2 uu____18379))
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
| uu____18388 -> begin
(fail2 "Pattern matching a non-inductive type")
end))
end
| uu____18390 -> begin
(

let uu____18392 = (

let uu____18394 = (FStar_Syntax_Print.term_to_string head_p)
in (

let uu____18396 = (FStar_Syntax_Print.term_to_string head_s)
in (FStar_Util.format2 "; head mismatch %s vs %s" uu____18394 uu____18396)))
in (fail2 uu____18392))
end))
end))
end
| uu____18399 -> begin
(

let uu____18400 = (FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t)
in (match (uu____18400) with
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

let uu____18437 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____18437) with
| (head1, args) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let uu____18501 = (FStar_TypeChecker_Env.lookup_datacon env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____18501) with
| (us, t_f) -> begin
(

let uu____18518 = (FStar_Syntax_Util.arrow_formals t_f)
in (match (uu____18518) with
| (formals, t) -> begin
((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
(fail1 "Pattern is not a fully-applied data constructor")
end
| uu____18582 -> begin
()
end);
(

let rec aux = (fun uu____18647 formals1 args1 -> (match (uu____18647) with
| (subst1, args_out, bvs, guard) -> begin
(match (((formals1), (args1))) with
| ([], []) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_uinst head1 us)
in (

let pat_e = (FStar_Syntax_Syntax.mk_Tm_app head2 args_out FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____18792 = (FStar_Syntax_Subst.subst subst1 t)
in ((pat_e), (uu____18792), (bvs), (guard)))))
end
| (((f1, uu____18798))::formals2, ((a, imp_a))::args2) -> begin
(

let t_f1 = (FStar_Syntax_Subst.subst subst1 f1.FStar_Syntax_Syntax.sort)
in (

let uu____18856 = (

let uu____18877 = (

let uu____18878 = (FStar_Syntax_Subst.compress a)
in uu____18878.FStar_Syntax_Syntax.n)
in (match (uu____18877) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let x1 = (

let uu___2415_18903 = x
in {FStar_Syntax_Syntax.ppname = uu___2415_18903.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2415_18903.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_f1})
in (

let a1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((f1), (a1))))::subst1
in ((((a1), (imp_a))), (subst2), ((FStar_List.append bvs ((x1)::[]))), (FStar_TypeChecker_Env.trivial_guard)))))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____18926) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_expected_typ env1 t_f1)
in (

let uu____18940 = (tc_tot_or_gtot_term env2 a)
in (match (uu____18940) with
| (a1, uu____18968, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env2 g)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((f1), (a1))))::subst1
in ((((a1), (imp_a))), (subst2), (bvs), (g1))))
end)))
end
| uu____18992 -> begin
(fail1 "Not a simple pattern")
end))
in (match (uu____18856) with
| (a1, subst2, bvs1, g) -> begin
(

let uu____19054 = (

let uu____19077 = (FStar_TypeChecker_Env.conj_guard g guard)
in ((subst2), ((FStar_List.append args_out ((a1)::[]))), (bvs1), (uu____19077)))
in (aux uu____19054 formals2 args2))
end)))
end
| uu____19116 -> begin
(fail1 "Not a fully applued pattern")
end)
end))
in (aux (([]), ([]), ([]), (FStar_TypeChecker_Env.trivial_guard)) formals args));
)
end))
end))
end
| uu____19172 -> begin
(fail1 "Not a simple pattern")
end)
end)))
in (

let rec check_nested_pattern = (fun env1 p t -> ((

let uu____19221 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Patterns")))
in (match (uu____19221) with
| true -> begin
(

let uu____19226 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____19228 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checking pattern %s at type %s\n" uu____19226 uu____19228)))
end
| uu____19231 -> begin
()
end));
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____19243) -> begin
(

let uu____19250 = (

let uu____19252 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Impossible: Expected an undecorated pattern, got %s" uu____19252))
in (failwith uu____19250))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___2447_19267 = x
in {FStar_Syntax_Syntax.ppname = uu___2447_19267.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2447_19267.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____19268 = (FStar_Syntax_Syntax.bv_to_name x1)
in (((x1)::[]), (uu____19268), ((

let uu___2450_19272 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___2450_19272.FStar_Syntax_Syntax.p})), (FStar_TypeChecker_Env.trivial_guard))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___2454_19275 = x
in {FStar_Syntax_Syntax.ppname = uu___2454_19275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2454_19275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____19276 = (FStar_Syntax_Syntax.bv_to_name x1)
in (((x1)::[]), (uu____19276), ((

let uu___2457_19280 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___2457_19280.FStar_Syntax_Syntax.p})), (FStar_TypeChecker_Env.trivial_guard))))
end
| FStar_Syntax_Syntax.Pat_constant (uu____19281) -> begin
(

let uu____19282 = (FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p)
in (match (uu____19282) with
| (uu____19304, e_c, uu____19306, uu____19307) -> begin
(

let uu____19312 = (tc_tot_or_gtot_term env1 e_c)
in (match (uu____19312) with
| (e_c1, lc, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
(

let expected_t = (expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t)
in ((

let uu____19335 = (

let uu____19337 = (FStar_TypeChecker_Rel.teq_nosmt_force env1 lc.FStar_Syntax_Syntax.res_typ expected_t)
in (not (uu____19337)))
in (match (uu____19335) with
| true -> begin
(

let uu____19340 = (

let uu____19342 = (FStar_Syntax_Print.term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____19344 = (FStar_Syntax_Print.term_to_string expected_t)
in (FStar_Util.format2 "Type of pattern (%s) does not match type of scrutinee (%s)" uu____19342 uu____19344)))
in (fail1 uu____19340))
end
| uu____19347 -> begin
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

let simple_sub_pats = (FStar_List.map (fun uu____19402 -> (match (uu____19402) with
| (p1, b) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____19432) -> begin
((p1), (b))
end
| uu____19442 -> begin
(

let uu____19443 = (

let uu____19446 = (

let uu____19447 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_var (uu____19447))
in (FStar_Syntax_Syntax.withinfo uu____19446 p1.FStar_Syntax_Syntax.p))
in ((uu____19443), (b)))
end)
end)) sub_pats)
in (

let uu___2485_19451 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), (simple_sub_pats))); FStar_Syntax_Syntax.p = uu___2485_19451.FStar_Syntax_Syntax.p}))
in (

let sub_pats1 = (FStar_All.pipe_right sub_pats (FStar_List.filter (fun uu____19496 -> (match (uu____19496) with
| (x, uu____19506) -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____19514) -> begin
false
end
| uu____19522 -> begin
true
end)
end))))
in (

let uu____19524 = (FStar_TypeChecker_PatternUtils.pat_as_exp false env1 simple_pat)
in (match (uu____19524) with
| (simple_bvs, simple_pat_e, g0, simple_pat_elab) -> begin
((match ((Prims.op_disEquality (FStar_List.length simple_bvs) (FStar_List.length sub_pats1))) with
| true -> begin
(

let uu____19561 = (

let uu____19563 = (FStar_Range.string_of_range p.FStar_Syntax_Syntax.p)
in (

let uu____19565 = (FStar_Syntax_Print.pat_to_string simple_pat)
in (

let uu____19567 = (FStar_Util.string_of_int (FStar_List.length sub_pats1))
in (

let uu____19574 = (FStar_Util.string_of_int (FStar_List.length simple_bvs))
in (FStar_Util.format4 "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s" uu____19563 uu____19565 uu____19567 uu____19574)))))
in (failwith uu____19561))
end
| uu____19577 -> begin
()
end);
(

let uu____19579 = (

let uu____19588 = (type_of_simple_pat env1 simple_pat_e)
in (match (uu____19588) with
| (simple_pat_e1, simple_pat_t, simple_bvs1, guard) -> begin
(

let g' = (

let uu____19616 = (expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t)
in (pat_typ_ok env1 simple_pat_t uu____19616))
in (

let guard1 = (FStar_TypeChecker_Env.conj_guard guard g')
in ((

let uu____19619 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Patterns")))
in (match (uu____19619) with
| true -> begin
(

let uu____19624 = (FStar_Syntax_Print.term_to_string simple_pat_e1)
in (

let uu____19626 = (FStar_Syntax_Print.term_to_string simple_pat_t)
in (

let uu____19628 = (

let uu____19630 = (FStar_List.map (fun x -> (

let uu____19638 = (

let uu____19640 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____19642 = (

let uu____19644 = (

let uu____19646 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (Prims.op_Hat uu____19646 ")"))
in (Prims.op_Hat " : " uu____19644))
in (Prims.op_Hat uu____19640 uu____19642)))
in (Prims.op_Hat "(" uu____19638))) simple_bvs1)
in (FStar_All.pipe_right uu____19630 (FStar_String.concat " ")))
in (FStar_Util.print3 "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n" uu____19624 uu____19626 uu____19628))))
end
| uu____19657 -> begin
()
end));
((simple_pat_e1), (simple_bvs1), (guard1));
)))
end))
in (match (uu____19579) with
| (simple_pat_e1, simple_bvs1, g1) -> begin
(

let uu____19678 = (

let uu____19700 = (

let uu____19722 = (FStar_TypeChecker_Env.conj_guard g0 g1)
in ((env1), ([]), ([]), ([]), (uu____19722)))
in (FStar_List.fold_left2 (fun uu____19783 uu____19784 x -> (match (((uu____19783), (uu____19784))) with
| ((env2, bvs, pats, subst1, g), (p1, b)) -> begin
(

let expected_t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____19917 = (check_nested_pattern env2 p1 expected_t)
in (match (uu____19917) with
| (bvs_p, e_p, p2, g') -> begin
(

let env3 = (FStar_TypeChecker_Env.push_bvs env2 bvs_p)
in (

let uu____19958 = (FStar_TypeChecker_Env.conj_guard g g')
in ((env3), ((FStar_List.append bvs bvs_p)), ((FStar_List.append pats ((((p2), (b)))::[]))), ((FStar_Syntax_Syntax.NT (((x), (e_p))))::subst1), (uu____19958))))
end)))
end)) uu____19700 sub_pats1 simple_bvs1))
in (match (uu____19678) with
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

let uu___2557_20170 = hd1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e1))); FStar_Syntax_Syntax.p = uu___2557_20170.FStar_Syntax_Syntax.p})
in (

let uu____20175 = (aux simple_pats1 bvs1 sub_pats2)
in (((hd2), (b)))::uu____20175)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(match (((bvs1), (sub_pats2))) with
| ((x')::bvs2, ((hd2, uu____20219))::sub_pats3) when (FStar_Syntax_Syntax.bv_eq x x') -> begin
(

let uu____20256 = (aux simple_pats1 bvs2 sub_pats3)
in (((hd2), (b)))::uu____20256)
end
| uu____20276 -> begin
(failwith "Impossible: simple pat variable mismatch")
end)
end
| uu____20302 -> begin
(failwith "Impossible: expected a simple pattern")
end)
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv1, simple_pats) -> begin
(

let nested_pats = (aux simple_pats simple_bvs1 checked_sub_pats)
in (

let uu___2578_20345 = pat
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv1), (nested_pats))); FStar_Syntax_Syntax.p = uu___2578_20345.FStar_Syntax_Syntax.p}))
end
| uu____20357 -> begin
(failwith "Impossible")
end)))
in (

let uu____20361 = (reconstruct_nested_pat simple_pat_elab)
in ((bvs), (pat_e), (uu____20361), (g)))))
end))
end));
)
end))))
end);
))
in ((

let uu____20365 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Patterns")))
in (match (uu____20365) with
| true -> begin
(

let uu____20370 = (FStar_Syntax_Print.pat_to_string p0)
in (FStar_Util.print1 "Checking pattern: %s\n" uu____20370))
end
| uu____20373 -> begin
()
end));
(

let uu____20375 = (

let uu____20386 = (

let uu___2583_20387 = (

let uu____20388 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____20388 FStar_Pervasives_Native.fst))
in {FStar_TypeChecker_Env.solver = uu___2583_20387.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___2583_20387.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___2583_20387.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___2583_20387.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___2583_20387.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___2583_20387.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___2583_20387.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___2583_20387.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___2583_20387.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___2583_20387.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___2583_20387.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___2583_20387.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___2583_20387.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___2583_20387.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___2583_20387.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___2583_20387.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___2583_20387.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = true; FStar_TypeChecker_Env.is_iface = uu___2583_20387.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___2583_20387.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___2583_20387.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___2583_20387.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___2583_20387.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___2583_20387.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___2583_20387.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___2583_20387.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___2583_20387.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___2583_20387.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___2583_20387.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___2583_20387.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___2583_20387.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___2583_20387.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___2583_20387.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___2583_20387.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___2583_20387.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___2583_20387.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___2583_20387.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___2583_20387.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___2583_20387.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___2583_20387.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___2583_20387.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___2583_20387.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___2583_20387.FStar_TypeChecker_Env.nbe})
in (

let uu____20404 = (FStar_TypeChecker_PatternUtils.elaborate_pat env p0)
in (check_nested_pattern uu____20386 uu____20404 pat_t)))
in (match (uu____20375) with
| (bvs, pat_e, pat, g) -> begin
((

let uu____20428 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Patterns")))
in (match (uu____20428) with
| true -> begin
(

let uu____20433 = (FStar_Syntax_Print.pat_to_string pat)
in (

let uu____20435 = (FStar_Syntax_Print.term_to_string pat_e)
in (FStar_Util.print2 "Done checking pattern %s as expression %s\n" uu____20433 uu____20435)))
end
| uu____20438 -> begin
()
end));
(

let uu____20440 = (FStar_TypeChecker_Env.push_bvs env bvs)
in (

let uu____20441 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env pat_e)
in ((pat), (bvs), (uu____20440), (pat_e), (uu____20441), (g))));
)
end));
)))))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp) * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____20487 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____20487) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____20533 = branch1
in (match (uu____20533) with
| (cpat, uu____20575, cbr) -> begin
(

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let uu____20597 = (

let uu____20604 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____20604 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____20597) with
| (scrutinee_env, uu____20638) -> begin
(

let uu____20643 = (tc_pat env pat_t pattern)
in (match (uu____20643) with
| (pattern1, pat_bvs1, pat_env, pat_exp, norm_pat_exp, guard_pat) -> begin
(

let uu____20694 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____20724 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____20724) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_WhenClauseNotSupported), ("When clauses are not yet supported in --verify mode; they will be some day")) e.FStar_Syntax_Syntax.pos)
end
| uu____20745 -> begin
(

let uu____20747 = (

let uu____20754 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_Syntax_Util.t_bool)
in (tc_term uu____20754 e))
in (match (uu____20747) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____20694) with
| (when_clause1, g_when) -> begin
(

let uu____20808 = (tc_term pat_env branch_exp)
in (match (uu____20808) with
| (branch_exp1, c, g_branch) -> begin
((FStar_TypeChecker_Env.def_check_guard_wf cbr.FStar_Syntax_Syntax.pos "tc_eqn.1" pat_env g_branch);
(

let when_condition = (match (when_clause1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____20864 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _20875 -> FStar_Pervasives_Native.Some (_20875)) uu____20864))
end)
in (

let uu____20876 = (

let eqs = (

let uu____20898 = (

let uu____20900 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____20900)))
in (match (uu____20898) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20909 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____20916) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____20931) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____20934) -> begin
FStar_Pervasives_Native.None
end
| uu____20937 -> begin
(

let uu____20938 = (

let uu____20941 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____20941 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____20938))
end))
end))
in (

let uu____20944 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch)
in (match (uu____20944) with
| (c1, g_branch1) -> begin
(

let uu____20971 = (match (((eqs), (when_condition))) with
| uu____20988 when (

let uu____21001 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____21001))) -> begin
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

let uu____21032 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____21033 = (FStar_TypeChecker_Env.imp_guard g g_when)
in ((uu____21032), (uu____21033))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____21054 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____21054))
in (

let uu____21055 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____21056 = (

let uu____21057 = (FStar_TypeChecker_Env.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Env.imp_guard uu____21057 g_when))
in ((uu____21055), (uu____21056))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Env.guard_of_guard_formula g_w)
in (

let uu____21075 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____21075), (g_when)))))
end)
in (match (uu____20971) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let maybe_return_c_weak = (fun should_return1 -> (

let c_weak1 = (

let uu____21118 = (should_return1 && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c_weak))
in (match (uu____21118) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env branch_exp1 c_weak)
end
| uu____21121 -> begin
c_weak
end))
in (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak1)))
in (

let uu____21123 = (FStar_TypeChecker_Env.close_guard env binders g_when_weak)
in (

let uu____21124 = (FStar_TypeChecker_Env.conj_guard guard_pat g_branch1)
in ((c_weak.FStar_Syntax_Syntax.eff_name), (c_weak.FStar_Syntax_Syntax.cflags), (maybe_return_c_weak), (uu____21123), (uu____21124))))))
end))
end)))
in (match (uu____20876) with
| (effect_label, cflags, maybe_return_c, g_when1, g_branch1) -> begin
(

let branch_guard = (

let uu____21175 = (

let uu____21177 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____21177)))
in (match (uu____21175) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____21180 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pattern2 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____21231 = (

let uu____21239 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____21239))
in (match (uu____21231) with
| (is_induc, datacons) -> begin
(match (((not (is_induc)) || ((FStar_List.length datacons) > (Prims.parse_int "1")))) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____21255 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____21255) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____21276 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____21292 = (

let uu____21297 = (

let uu____21298 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____21298)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____21297))
in (uu____21292 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____21323 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____21323)::[])))
end)))
end
| uu____21324 -> begin
[]
end)
end)))
in (

let fail1 = (fun uu____21331 -> (

let uu____21332 = (

let uu____21334 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____21336 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____21338 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____21334 uu____21336 uu____21338))))
in (failwith uu____21332)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____21353) -> begin
(head_constructor t1)
end
| uu____21358 -> begin
(fail1 ())
end))
in (

let force_scrutinee = (fun uu____21364 -> (match (scrutinee_tm1) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21365 = (

let uu____21367 = (FStar_Range.string_of_range pattern2.FStar_Syntax_Syntax.p)
in (

let uu____21369 = (FStar_Syntax_Print.pat_to_string pattern2)
in (FStar_Util.format2 "Impossible (%s): scrutinee of match is not defined %s" uu____21367 uu____21369)))
in (failwith uu____21365))
end
| FStar_Pervasives_Native.Some (t) -> begin
t
end))
in (

let pat_exp2 = (

let uu____21376 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____21376 FStar_Syntax_Util.unmeta))
in (match (((pattern2.FStar_Syntax_Syntax.v), (pat_exp2.FStar_Syntax_Syntax.n))) with
| (uu____21381, FStar_Syntax_Syntax.Tm_name (uu____21382)) -> begin
[]
end
| (uu____21383, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| (FStar_Syntax_Syntax.Pat_constant (_c), FStar_Syntax_Syntax.Tm_constant (c1)) -> begin
(

let uu____21386 = (

let uu____21387 = (tc_constant env pat_exp2.FStar_Syntax_Syntax.pos c1)
in (

let uu____21388 = (force_scrutinee ())
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____21387 uu____21388 pat_exp2)))
in (uu____21386)::[])
end
| (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (uu____21389, FStar_Pervasives_Native.Some (uu____21390))), uu____21391) -> begin
(

let uu____21408 = (

let uu____21415 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____21415) with
| (env1, uu____21429) -> begin
(env1.FStar_TypeChecker_Env.type_of env1 pat_exp2)
end))
in (match (uu____21408) with
| (uu____21436, t, uu____21438) -> begin
(

let uu____21439 = (

let uu____21440 = (force_scrutinee ())
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero t uu____21440 pat_exp2))
in (uu____21439)::[])
end))
end
| (FStar_Syntax_Syntax.Pat_cons (uu____21441, []), FStar_Syntax_Syntax.Tm_uinst (uu____21442)) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____21466 = (

let uu____21468 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____21468)))
in (match (uu____21466) with
| true -> begin
(failwith "Impossible: nullary patterns must be data constructors")
end
| uu____21476 -> begin
(

let uu____21478 = (force_scrutinee ())
in (

let uu____21481 = (head_constructor pat_exp2)
in (discriminate uu____21478 uu____21481)))
end)))
end
| (FStar_Syntax_Syntax.Pat_cons (uu____21484, []), FStar_Syntax_Syntax.Tm_fvar (uu____21485)) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____21503 = (

let uu____21505 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____21505)))
in (match (uu____21503) with
| true -> begin
(failwith "Impossible: nullary patterns must be data constructors")
end
| uu____21513 -> begin
(

let uu____21515 = (force_scrutinee ())
in (

let uu____21518 = (head_constructor pat_exp2)
in (discriminate uu____21515 uu____21518)))
end)))
end
| (FStar_Syntax_Syntax.Pat_cons (uu____21521, pat_args), FStar_Syntax_Syntax.Tm_app (head1, args)) -> begin
(

let f = (head_constructor head1)
in (

let uu____21568 = ((

let uu____21572 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____21572))) || (Prims.op_disEquality (FStar_List.length pat_args) (FStar_List.length args)))
in (match (uu____21568) with
| true -> begin
(failwith "Impossible: application patterns must be fully-applied data constructors")
end
| uu____21595 -> begin
(

let sub_term_guards = (

let uu____21600 = (

let uu____21605 = (FStar_List.zip pat_args args)
in (FStar_All.pipe_right uu____21605 (FStar_List.mapi (fun i uu____21691 -> (match (uu____21691) with
| ((pi, uu____21713), (ei, uu____21715)) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let scrutinee_tm2 = (

let uu____21743 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____21743) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| uu____21764 -> begin
(

let proj = (

let uu____21776 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar uu____21776 (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____21778 = (

let uu____21779 = (

let uu____21784 = (

let uu____21785 = (

let uu____21794 = (force_scrutinee ())
in (FStar_Syntax_Syntax.as_arg uu____21794))
in (uu____21785)::[])
in (FStar_Syntax_Syntax.mk_Tm_app proj uu____21784))
in (uu____21779 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in FStar_Pervasives_Native.Some (uu____21778)))
end))
in (build_branch_guard scrutinee_tm2 pi ei)))
end)))))
in (FStar_All.pipe_right uu____21600 FStar_List.flatten))
in (

let uu____21817 = (

let uu____21820 = (force_scrutinee ())
in (discriminate uu____21820 f))
in (FStar_List.append uu____21817 sub_term_guards)))
end)))
end
| (FStar_Syntax_Syntax.Pat_dot_term (uu____21823), uu____21824) -> begin
[]
end
| uu____21831 -> begin
(

let uu____21836 = (

let uu____21838 = (FStar_Syntax_Print.pat_to_string pattern2)
in (

let uu____21840 = (FStar_Syntax_Print.term_to_string pat_exp2)
in (FStar_Util.format2 "Internal error: unexpected elaborated pattern: %s and pattern expression %s" uu____21838 uu____21840)))
in (failwith uu____21836))
end)))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pattern2 pat -> (

let uu____21869 = (

let uu____21871 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____21871)))
in (match (uu____21869) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____21874 -> begin
(

let t = (

let uu____21877 = (build_branch_guard scrutinee_tm1 pattern2 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____21877))
in (

let uu____21886 = (FStar_Syntax_Util.type_u ())
in (match (uu____21886) with
| (k, uu____21892) -> begin
(

let uu____21893 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____21893) with
| (t1, uu____21901, uu____21902) -> begin
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

let uu____21914 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____21914) with
| true -> begin
(

let uu____21917 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____21917))
end
| uu____21921 -> begin
()
end));
(

let uu____21923 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in (

let uu____21940 = (

let uu____21941 = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (FStar_TypeChecker_Util.close_guard_implicits env uu____21941 guard))
in ((uu____21923), (branch_guard), (effect_label), (cflags), (maybe_return_c), (uu____21940))));
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

let uu____21988 = (check_let_bound_def true env1 lb)
in (match (uu____21988) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____22014 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____22036 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____22036), (univ_vars1), (c1)))
end
| uu____22039 -> begin
(

let g11 = (

let uu____22042 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____22042 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let uu____22043 = (

let uu____22056 = (

let uu____22071 = (

let uu____22080 = (

let uu____22087 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____22087)))
in (uu____22080)::[])
in (FStar_TypeChecker_Util.generalize env1 false uu____22071))
in (FStar_List.hd uu____22056))
in (match (uu____22043) with
| (uu____22123, univs1, e11, c11, gvs) -> begin
(

let g12 = (FStar_All.pipe_left (FStar_TypeChecker_Env.map_guard g11) (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env1))
in (

let g13 = (FStar_TypeChecker_Env.abstract_guard_n gvs g12)
in (

let uu____22137 = (FStar_Syntax_Util.lcomp_of_comp c11)
in ((g13), (e11), (univs1), (uu____22137)))))
end)))
end)
in (match (uu____22014) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____22154 = (

let uu____22163 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____22163) with
| true -> begin
(

let uu____22174 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____22174) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____22205 -> begin
((

let uu____22208 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____22208 FStar_TypeChecker_Err.top_level_effect));
(

let uu____22209 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____22209), (c12)));
)
end)
end))
end
| uu____22218 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____22224 = (FStar_Syntax_Syntax.lcomp_comp c11)
in (FStar_All.pipe_right uu____22224 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env1)))
in (

let e21 = (

let uu____22230 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____22230) with
| true -> begin
e2
end
| uu____22235 -> begin
((

let uu____22238 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____22238 FStar_TypeChecker_Err.top_level_effect));
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos);
)
end))
in ((e21), (c))));
)
end))
in (match (uu____22154) with
| (e21, c12) -> begin
((

let uu____22262 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____22262) with
| true -> begin
(

let uu____22265 = (FStar_Syntax_Print.term_to_string e11)
in (FStar_Util.print1 "Let binding BEFORE tcnorm: %s\n" uu____22265))
end
| uu____22268 -> begin
()
end));
(

let e12 = (

let uu____22271 = (FStar_Options.tcnorm ())
in (match (uu____22271) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldAttr ((FStar_Parser_Const.tcnorm_attr)::[]))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env1 e11)
end
| uu____22274 -> begin
e11
end))
in ((

let uu____22277 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____22277) with
| true -> begin
(

let uu____22280 = (FStar_Syntax_Print.term_to_string e12)
in (FStar_Util.print1 "Let binding AFTER tcnorm: %s\n" uu____22280))
end
| uu____22283 -> begin
()
end));
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit)
in (

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e12 lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
in (

let uu____22289 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____22303 = (FStar_Syntax_Util.lcomp_of_comp cres)
in ((uu____22289), (uu____22303), (FStar_TypeChecker_Env.trivial_guard))))));
));
)
end))
end))
end))
end
| uu____22304 -> begin
(failwith "Impossible")
end)))
and maybe_intro_smt_lemma : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lem_typ c2 -> (

let uu____22315 = (FStar_Syntax_Util.is_smt_lemma lem_typ)
in (match (uu____22315) with
| true -> begin
(

let universe_of_binders = (fun bs -> (

let uu____22342 = (FStar_List.fold_left (fun uu____22367 b -> (match (uu____22367) with
| (env1, us) -> begin
(

let u = (env1.FStar_TypeChecker_Env.universe_of env1 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((env2), ((u)::us))))
end)) ((env), ([])) bs)
in (match (uu____22342) with
| (uu____22415, us) -> begin
(FStar_List.rev us)
end)))
in (

let quant = (FStar_Syntax_Util.smt_lemma_as_forall lem_typ universe_of_binders)
in (FStar_TypeChecker_Util.weaken_precondition env c2 (FStar_TypeChecker_Common.NonTrivial (quant)))))
end
| uu____22422 -> begin
c2
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___2895_22451 = env1
in {FStar_TypeChecker_Env.solver = uu___2895_22451.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___2895_22451.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___2895_22451.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___2895_22451.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___2895_22451.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___2895_22451.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___2895_22451.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___2895_22451.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___2895_22451.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___2895_22451.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___2895_22451.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___2895_22451.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___2895_22451.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___2895_22451.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___2895_22451.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___2895_22451.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___2895_22451.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___2895_22451.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___2895_22451.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___2895_22451.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___2895_22451.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___2895_22451.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___2895_22451.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___2895_22451.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___2895_22451.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___2895_22451.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___2895_22451.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___2895_22451.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___2895_22451.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___2895_22451.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___2895_22451.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___2895_22451.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___2895_22451.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___2895_22451.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___2895_22451.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___2895_22451.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___2895_22451.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___2895_22451.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___2895_22451.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___2895_22451.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___2895_22451.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___2895_22451.FStar_TypeChecker_Env.nbe})
in (

let uu____22453 = (

let uu____22465 = (

let uu____22466 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____22466 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____22465 lb))
in (match (uu____22453) with
| (e1, uu____22489, c1, g1, annotated) -> begin
(

let pure_or_ghost = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c1)
in (

let is_inline_let = (FStar_Util.for_some (FStar_Syntax_Util.is_fvar FStar_Parser_Const.inline_let_attr) lb.FStar_Syntax_Syntax.lbattrs)
in ((match ((is_inline_let && (not (pure_or_ghost)))) with
| true -> begin
(

let uu____22503 = (

let uu____22509 = (

let uu____22511 = (FStar_Syntax_Print.term_to_string e1)
in (

let uu____22513 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.format2 "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\"" uu____22511 uu____22513)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____22509)))
in (FStar_Errors.raise_error uu____22503 e1.FStar_Syntax_Syntax.pos))
end
| uu____22517 -> begin
()
end);
(

let attrs = (

let uu____22524 = ((pure_or_ghost && (not (is_inline_let))) && (FStar_Syntax_Util.is_unit c1.FStar_Syntax_Syntax.res_typ))
in (match (uu____22524) with
| true -> begin
(FStar_Syntax_Util.inline_let_attr)::lb.FStar_Syntax_Syntax.lbattrs
end
| uu____22533 -> begin
lb.FStar_Syntax_Syntax.lbattrs
end))
in (

let x = (

let uu___2910_22536 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___2910_22536.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2910_22536.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____22537 = (

let uu____22542 = (

let uu____22543 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____22543)::[])
in (FStar_Syntax_Subst.open_term uu____22542 e2))
in (match (uu____22537) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let env_x = (FStar_TypeChecker_Env.push_bv env2 x1)
in (

let uu____22587 = (tc_term env_x e21)
in (match (uu____22587) with
| (e22, c2, g2) -> begin
(

let c21 = (maybe_intro_smt_lemma env_x c1.FStar_Syntax_Syntax.res_typ c2)
in (

let cres = (FStar_TypeChecker_Util.maybe_return_e2_and_bind e1.FStar_Syntax_Syntax.pos env2 (FStar_Pervasives_Native.Some (e1)) c1 e22 ((FStar_Pervasives_Native.Some (x1)), (c21)))
in (

let e11 = (FStar_TypeChecker_Util.maybe_lift env2 e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e23 = (FStar_TypeChecker_Util.maybe_lift env2 e22 c21.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c21.FStar_Syntax_Syntax.res_typ)
in (

let lb1 = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x1)) [] c1.FStar_Syntax_Syntax.res_typ cres.FStar_Syntax_Syntax.eff_name e11 attrs lb.FStar_Syntax_Syntax.lbpos)
in (

let e3 = (

let uu____22613 = (

let uu____22620 = (

let uu____22621 = (

let uu____22635 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____22635)))
in FStar_Syntax_Syntax.Tm_let (uu____22621))
in (FStar_Syntax_Syntax.mk uu____22620))
in (uu____22613 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____22653 = (

let uu____22654 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____22655 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____22654 c1.FStar_Syntax_Syntax.res_typ uu____22655 e11)))
in (FStar_All.pipe_left (fun _22656 -> FStar_TypeChecker_Common.NonTrivial (_22656)) uu____22653))
in (

let g21 = (

let uu____22658 = (

let uu____22659 = (FStar_TypeChecker_Env.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Env.imp_guard uu____22659 g2))
in (FStar_TypeChecker_Env.close_guard env2 xb uu____22658))
in (

let g22 = (FStar_TypeChecker_Util.close_guard_implicits env2 xb g21)
in (

let guard = (FStar_TypeChecker_Env.conj_guard g1 g22)
in (

let uu____22662 = (

let uu____22664 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____22664))
in (match (uu____22662) with
| true -> begin
(

let tt = (

let uu____22675 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____22675 FStar_Option.get))
in ((

let uu____22681 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____22681) with
| true -> begin
(

let uu____22686 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____22688 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____22686 uu____22688)))
end
| uu____22691 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____22693 -> begin
(

let uu____22695 = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____22695) with
| (t, g_ex) -> begin
((

let uu____22709 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____22709) with
| true -> begin
(

let uu____22714 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____22716 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____22714 uu____22716)))
end
| uu____22719 -> begin
()
end));
(

let uu____22721 = (FStar_TypeChecker_Env.conj_guard g_ex guard)
in ((e4), ((

let uu___2943_22723 = cres
in {FStar_Syntax_Syntax.eff_name = uu___2943_22723.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___2943_22723.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___2943_22723.FStar_Syntax_Syntax.comp_thunk})), (uu____22721)));
)
end))
end)))))))))))))
end)))))
end))));
)))
end)))
end
| uu____22724 -> begin
(failwith "Impossible (inner let with more than one lb)")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____22760 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____22760) with
| (lbs1, e21) -> begin
(

let uu____22779 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____22779) with
| (env0, topt) -> begin
(

let uu____22798 = (build_let_rec_env true env0 lbs1)
in (match (uu____22798) with
| (lbs2, rec_env, g_t) -> begin
(

let uu____22821 = (check_let_recs rec_env lbs2)
in (match (uu____22821) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____22841 = (

let uu____22842 = (FStar_TypeChecker_Env.conj_guard g_t g_lbs)
in (FStar_All.pipe_right uu____22842 (FStar_TypeChecker_Rel.solve_deferred_constraints env1)))
in (FStar_All.pipe_right uu____22841 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let all_lb_names = (

let uu____22848 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____22848 (fun _22865 -> FStar_Pervasives_Native.Some (_22865))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((Prims.op_Equality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
lb
end
| uu____22883 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)))))
end
| uu____22885 -> begin
(

let ecs = (

let uu____22902 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____22936 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____22936))))))
in (FStar_TypeChecker_Util.generalize env1 true uu____22902))
in (FStar_List.map2 (fun uu____22971 lb -> (match (uu____22971) with
| (x, uvs, e, c, gvs) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)) ecs lbs3))
end)
in (

let cres = (

let uu____23019 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____23019))
in (

let uu____23020 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____23020) with
| (lbs5, e22) -> begin
((

let uu____23040 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____23040 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____23041 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____23041), (cres), (FStar_TypeChecker_Env.trivial_guard)));
)
end))))))
end))
end))
end))
end))
end
| uu____23055 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____23091 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____23091) with
| (lbs1, e21) -> begin
(

let uu____23110 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____23110) with
| (env0, topt) -> begin
(

let uu____23129 = (build_let_rec_env false env0 lbs1)
in (match (uu____23129) with
| (lbs2, rec_env, g_t) -> begin
(

let uu____23152 = (

let uu____23159 = (check_let_recs rec_env lbs2)
in (FStar_All.pipe_right uu____23159 (fun uu____23182 -> (match (uu____23182) with
| (lbs3, g) -> begin
(

let uu____23201 = (FStar_TypeChecker_Env.conj_guard g_t g)
in ((lbs3), (uu____23201)))
end))))
in (match (uu____23152) with
| (lbs3, g_lbs) -> begin
(

let uu____23216 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___3018_23239 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___3018_23239.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3018_23239.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___3021_23241 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___3021_23241.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___3021_23241.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___3021_23241.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___3021_23241.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___3021_23241.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___3021_23241.FStar_Syntax_Syntax.lbpos})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____23216) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____23268 = (tc_term env2 e21)
in (match (uu____23268) with
| (e22, cres, g2) -> begin
(

let cres1 = (FStar_List.fold_right (fun lb cres1 -> (maybe_intro_smt_lemma env2 lb.FStar_Syntax_Syntax.lbtyp cres1)) lbs4 cres)
in (

let cres2 = (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e22 cres1)
in (

let cres3 = (FStar_Syntax_Util.lcomp_set_flags cres2 ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
in (

let guard = (

let uu____23292 = (

let uu____23293 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Env.close_guard env2 uu____23293 g2))
in (FStar_TypeChecker_Env.conj_guard g_lbs uu____23292))
in (

let cres4 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres3)
in (

let tres = (norm env2 cres4.FStar_Syntax_Syntax.res_typ)
in (

let cres5 = (

let uu___3042_23303 = cres4
in {FStar_Syntax_Syntax.eff_name = uu___3042_23303.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___3042_23303.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___3042_23303.FStar_Syntax_Syntax.comp_thunk})
in (

let guard1 = (

let bs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (

let uu____23311 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____23311)))))
in (FStar_TypeChecker_Util.close_guard_implicits env2 bs guard))
in (

let uu____23312 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____23312) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____23353) -> begin
((e), (cres5), (guard1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____23354 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (match (uu____23354) with
| (tres1, g_ex) -> begin
(

let cres6 = (

let uu___3058_23368 = cres5
in {FStar_Syntax_Syntax.eff_name = uu___3058_23368.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___3058_23368.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___3058_23368.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____23369 = (FStar_TypeChecker_Env.conj_guard g_ex guard1)
in ((e), (cres6), (uu____23369))))
end))
end))
end))))))))))
end)))
end))
end))
end))
end))
end))
end
| uu____23370 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Env.guard_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let uu____23418 = (FStar_Options.ml_ish ())
in (match (uu____23418) with
| true -> begin
false
end
| uu____23423 -> begin
(

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____23426 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____23426) with
| (formals, c) -> begin
(

let uu____23458 = (FStar_Syntax_Util.abs_formals lbdef)
in (match (uu____23458) with
| (actuals, uu____23469, uu____23470) -> begin
(match ((((FStar_List.length formals) < (Prims.parse_int "1")) || ((FStar_List.length actuals) < (Prims.parse_int "1")))) with
| true -> begin
(

let uu____23491 = (

let uu____23497 = (

let uu____23499 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____23501 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____23499 uu____23501)))
in ((FStar_Errors.Fatal_RecursiveFunctionLiteral), (uu____23497)))
in (FStar_Errors.raise_error uu____23491 lbtyp.FStar_Syntax_Syntax.pos))
end
| uu____23506 -> begin
(

let actuals1 = (

let uu____23509 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____23509 actuals))
in ((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____23538 -> begin
(

let uu____23540 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____23540))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____23557 -> begin
(

let uu____23559 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____23559))
end))
in (

let msg = (

let uu____23564 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____23566 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____23564 uu____23566 formals_msg actuals_msg)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_LetRecArgumentMismatch), (msg)) lbdef.FStar_Syntax_Syntax.pos))))
end
| uu____23570 -> begin
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

let uu____23578 = (FStar_List.fold_left (fun uu____23611 lb -> (match (uu____23611) with
| (lbs1, env1, g_acc) -> begin
(

let uu____23636 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____23636) with
| (univ_vars1, t, check_t) -> begin
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univ_vars1)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____23659 = (match ((not (check_t))) with
| true -> begin
((g_acc), (t))
end
| uu____23675 -> begin
(

let env01 = (FStar_TypeChecker_Env.push_univ_vars env0 univ_vars1)
in (

let uu____23678 = (

let uu____23685 = (

let uu____23686 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____23686))
in (tc_check_tot_or_gtot_term (

let uu___3104_23697 = env01
in {FStar_TypeChecker_Env.solver = uu___3104_23697.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3104_23697.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3104_23697.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3104_23697.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3104_23697.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3104_23697.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3104_23697.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___3104_23697.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___3104_23697.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3104_23697.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3104_23697.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3104_23697.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3104_23697.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3104_23697.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3104_23697.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___3104_23697.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___3104_23697.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3104_23697.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3104_23697.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___3104_23697.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___3104_23697.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3104_23697.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3104_23697.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3104_23697.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3104_23697.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3104_23697.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3104_23697.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3104_23697.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3104_23697.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___3104_23697.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3104_23697.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3104_23697.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3104_23697.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3104_23697.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3104_23697.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3104_23697.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3104_23697.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3104_23697.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3104_23697.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3104_23697.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3104_23697.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3104_23697.FStar_TypeChecker_Env.nbe}) t uu____23685))
in (match (uu____23678) with
| (t1, uu____23706, g) -> begin
(

let uu____23708 = (

let uu____23709 = (

let uu____23710 = (FStar_All.pipe_right g (FStar_TypeChecker_Rel.resolve_implicits env2))
in (FStar_All.pipe_right uu____23710 (FStar_TypeChecker_Rel.discharge_guard env2)))
in (FStar_TypeChecker_Env.conj_guard g_acc uu____23709))
in (

let uu____23711 = (norm env01 t1)
in ((uu____23708), (uu____23711))))
end)))
end)
in (match (uu____23659) with
| (g, t1) -> begin
(

let env3 = (

let uu____23731 = (termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1)
in (match (uu____23731) with
| true -> begin
(

let uu___3114_23734 = env2
in {FStar_TypeChecker_Env.solver = uu___3114_23734.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3114_23734.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3114_23734.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3114_23734.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3114_23734.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3114_23734.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3114_23734.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___3114_23734.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___3114_23734.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3114_23734.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3114_23734.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3114_23734.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3114_23734.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3114_23734.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1), (univ_vars1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___3114_23734.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___3114_23734.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3114_23734.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3114_23734.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3114_23734.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___3114_23734.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___3114_23734.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3114_23734.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3114_23734.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3114_23734.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3114_23734.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3114_23734.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3114_23734.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3114_23734.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3114_23734.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___3114_23734.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3114_23734.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3114_23734.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3114_23734.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3114_23734.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3114_23734.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3114_23734.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3114_23734.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3114_23734.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3114_23734.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3114_23734.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3114_23734.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3114_23734.FStar_TypeChecker_Env.nbe})
end
| uu____23741 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname ((univ_vars1), (t1)))
end))
in (

let lb1 = (

let uu___3117_23748 = lb
in {FStar_Syntax_Syntax.lbname = uu___3117_23748.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___3117_23748.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___3117_23748.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___3117_23748.FStar_Syntax_Syntax.lbpos})
in (((lb1)::lbs1), (env3), (g))))
end))))
end))
end)) (([]), (env), (FStar_TypeChecker_Env.trivial_guard)) lbs)
in (match (uu____23578) with
| (lbs1, env1, g) -> begin
(((FStar_List.rev lbs1)), (env1), (g))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____23774 = (

let uu____23783 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____23809 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____23809) with
| (bs, t, lcomp) -> begin
(match (bs) with
| [] -> begin
(

let uu____23839 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_RecursiveFunctionLiteral), ("Only function literals may be defined recursively")) uu____23839))
end
| uu____23846 -> begin
(

let lb1 = (

let uu___3134_23849 = lb
in (

let uu____23850 = (FStar_Syntax_Util.abs bs t lcomp)
in {FStar_Syntax_Syntax.lbname = uu___3134_23849.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___3134_23849.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___3134_23849.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___3134_23849.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____23850; FStar_Syntax_Syntax.lbattrs = uu___3134_23849.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___3134_23849.FStar_Syntax_Syntax.lbpos}))
in (

let uu____23853 = (

let uu____23860 = (FStar_TypeChecker_Env.set_expected_typ env lb1.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____23860 lb1.FStar_Syntax_Syntax.lbdef))
in (match (uu____23853) with
| (e, c, g) -> begin
((

let uu____23869 = (

let uu____23871 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____23871)))
in (match (uu____23869) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedGTotForLetRec), ("Expected let rec to be a Tot term; got effect GTot")) e.FStar_Syntax_Syntax.pos)
end
| uu____23876 -> begin
()
end));
(

let lb2 = (FStar_Syntax_Util.mk_letbinding lb1.FStar_Syntax_Syntax.lbname lb1.FStar_Syntax_Syntax.lbunivs lb1.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e lb1.FStar_Syntax_Syntax.lbattrs lb1.FStar_Syntax_Syntax.lbpos)
in ((lb2), (g)));
)
end)))
end)
end)))))
in (FStar_All.pipe_right uu____23783 FStar_List.unzip))
in (match (uu____23774) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs FStar_TypeChecker_Env.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____23927 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____23927) with
| (env1, uu____23946) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____23954 = (check_lbtyp top_level env lb)
in (match (uu____23954) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (Prims.op_disEquality univ_vars1 []))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UniversePolymorphicInnerLetBound), ("Inner let-bound definitions cannot be universe polymorphic")) e1.FStar_Syntax_Syntax.pos)
end
| uu____23999 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____24003 = (tc_maybe_toplevel_term (

let uu___3165_24012 = env11
in {FStar_TypeChecker_Env.solver = uu___3165_24012.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3165_24012.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3165_24012.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3165_24012.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3165_24012.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3165_24012.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3165_24012.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___3165_24012.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___3165_24012.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3165_24012.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3165_24012.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3165_24012.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3165_24012.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3165_24012.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3165_24012.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___3165_24012.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3165_24012.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3165_24012.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3165_24012.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___3165_24012.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___3165_24012.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3165_24012.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3165_24012.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3165_24012.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3165_24012.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3165_24012.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3165_24012.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3165_24012.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3165_24012.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___3165_24012.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3165_24012.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3165_24012.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3165_24012.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3165_24012.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3165_24012.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3165_24012.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3165_24012.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3165_24012.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3165_24012.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3165_24012.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3165_24012.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3165_24012.FStar_TypeChecker_Env.nbe}) e11)
in (match (uu____24003) with
| (e12, c1, g1) -> begin
(

let uu____24027 = (

let uu____24032 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____24038 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____24032 e12 c1 wf_annot))
in (match (uu____24027) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Env.conj_guard g1 guard_f)
in ((

let uu____24055 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____24055) with
| true -> begin
(

let uu____24058 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____24060 = (FStar_Syntax_Print.lcomp_to_string c11)
in (

let uu____24062 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked let-bound def %s : %s guard is %s\n" uu____24058 uu____24060 uu____24062))))
end
| uu____24065 -> begin
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

let uu____24101 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____24101) with
| (univ_opening, univ_vars1) -> begin
(

let uu____24134 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in ((FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard), (univ_vars1), (univ_opening), (uu____24134)))
end))
end
| uu____24139 -> begin
(

let uu____24140 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____24140) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____24190 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Env.trivial_guard), (univ_vars1), (univ_opening), (uu____24190)))
end
| uu____24195 -> begin
(

let uu____24197 = (FStar_Syntax_Util.type_u ())
in (match (uu____24197) with
| (k, uu____24217) -> begin
(

let uu____24218 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____24218) with
| (t2, uu____24240, g) -> begin
((

let uu____24243 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____24243) with
| true -> begin
(

let uu____24246 = (

let uu____24248 = (FStar_Syntax_Util.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____24248))
in (

let uu____24249 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____24246 uu____24249)))
end
| uu____24252 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____24255 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____24255))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____24261 -> (match (uu____24261) with
| (x, imp) -> begin
(

let uu____24288 = (FStar_Syntax_Util.type_u ())
in (match (uu____24288) with
| (tu, u) -> begin
((

let uu____24310 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____24310) with
| true -> begin
(

let uu____24313 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____24315 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____24317 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binder %s:%s at type %s\n" uu____24313 uu____24315 uu____24317))))
end
| uu____24320 -> begin
()
end));
(

let uu____24322 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____24322) with
| (t, uu____24344, g) -> begin
(

let uu____24346 = (match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau)) -> begin
(

let uu____24362 = (tc_tactic env tau)
in (match (uu____24362) with
| (tau1, uu____24376, g1) -> begin
((FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau1))), (g1))
end))
end
| uu____24380 -> begin
((imp), (FStar_TypeChecker_Env.trivial_guard))
end)
in (match (uu____24346) with
| (imp1, g') -> begin
(

let x1 = (((

let uu___3227_24415 = x
in {FStar_Syntax_Syntax.ppname = uu___3227_24415.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3227_24415.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp1))
in ((

let uu____24417 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____24417) with
| true -> begin
(

let uu____24420 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____24424 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____24420 uu____24424)))
end
| uu____24427 -> begin
()
end));
(

let uu____24429 = (push_binding env x1)
in ((x1), (uu____24429), (g), (u)));
))
end))
end));
)
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes) = (fun env bs -> ((

let uu____24441 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____24441) with
| true -> begin
(

let uu____24444 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Checking binders %s\n" uu____24444))
end
| uu____24448 -> begin
()
end));
(

let rec aux = (fun env1 bs1 -> (match (bs1) with
| [] -> begin
(([]), (env1), (FStar_TypeChecker_Env.trivial_guard), ([]))
end
| (b)::bs2 -> begin
(

let uu____24557 = (tc_binder env1 b)
in (match (uu____24557) with
| (b1, env', g, u) -> begin
(

let uu____24606 = (aux env' bs2)
in (match (uu____24606) with
| (bs3, env'1, g', us) -> begin
(

let uu____24667 = (

let uu____24668 = (FStar_TypeChecker_Env.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Env.conj_guard g uu____24668))
in (((b1)::bs3), (env'1), (uu____24667), ((u)::us)))
end))
end))
end))
in (aux env bs));
))
and tc_smt_pats : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun en pats -> (

let tc_args = (fun en1 args -> (FStar_List.fold_right (fun uu____24776 uu____24777 -> (match (((uu____24776), (uu____24777))) with
| ((t, imp), (args1, g)) -> begin
((FStar_All.pipe_right t (check_no_smt_theory_symbols en1));
(

let uu____24869 = (tc_term en1 t)
in (match (uu____24869) with
| (t1, uu____24889, g') -> begin
(

let uu____24891 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____24891)))
end));
)
end)) args (([]), (FStar_TypeChecker_Env.trivial_guard))))
in (FStar_List.fold_right (fun p uu____24945 -> (match (uu____24945) with
| (pats1, g) -> begin
(

let uu____24972 = (tc_args en p)
in (match (uu____24972) with
| (args, g') -> begin
(

let uu____24985 = (FStar_TypeChecker_Env.conj_guard g g')
in (((args)::pats1), (uu____24985)))
end))
end)) pats (([]), (FStar_TypeChecker_Env.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____24998 = (tc_maybe_toplevel_term env e)
in (match (uu____24998) with
| (e1, c, g) -> begin
(

let uu____25014 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____25014) with
| true -> begin
((e1), (c), (g))
end
| uu____25023 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (FStar_Syntax_Syntax.lcomp_comp c)
in (

let c2 = (norm_c env c1)
in (

let uu____25028 = (

let uu____25034 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____25034) with
| true -> begin
(

let uu____25042 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____25042), (false)))
end
| uu____25045 -> begin
(

let uu____25047 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____25047), (true)))
end))
in (match (uu____25028) with
| (target_comp, allow_ghost) -> begin
(

let uu____25060 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____25060) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____25070 = (FStar_Syntax_Util.lcomp_of_comp target_comp)
in (

let uu____25071 = (FStar_TypeChecker_Env.conj_guard g1 g')
in ((e1), (uu____25070), (uu____25071))))
end
| uu____25072 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____25082 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in (FStar_Errors.raise_error uu____25082 e1.FStar_Syntax_Syntax.pos))
end
| uu____25094 -> begin
(

let uu____25096 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in (FStar_Errors.raise_error uu____25096 e1.FStar_Syntax_Syntax.pos))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____25120 = (tc_tot_or_gtot_term env t)
in (match (uu____25120) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____25153 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____25153) with
| true -> begin
(

let uu____25158 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____25158))
end
| uu____25161 -> begin
()
end));
(

let env1 = (

let uu___3309_25164 = env
in {FStar_TypeChecker_Env.solver = uu___3309_25164.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3309_25164.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3309_25164.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3309_25164.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3309_25164.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3309_25164.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3309_25164.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___3309_25164.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___3309_25164.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3309_25164.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3309_25164.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3309_25164.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3309_25164.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3309_25164.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___3309_25164.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3309_25164.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3309_25164.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3309_25164.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___3309_25164.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___3309_25164.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3309_25164.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3309_25164.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3309_25164.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3309_25164.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3309_25164.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3309_25164.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3309_25164.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3309_25164.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___3309_25164.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3309_25164.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3309_25164.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3309_25164.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3309_25164.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3309_25164.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3309_25164.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3309_25164.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3309_25164.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3309_25164.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3309_25164.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3309_25164.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3309_25164.FStar_TypeChecker_Env.nbe})
in (

let uu____25172 = (FStar_All.try_with (fun uu___3313_25186 -> (match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)) (fun uu___3312_25198 -> (match (uu___3312_25198) with
| FStar_Errors.Error (e1, msg, uu____25207) -> begin
(

let uu____25210 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((e1), (msg)) uu____25210))
end)))
in (match (uu____25172) with
| (t, c, g) -> begin
(

let uu____25227 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____25227) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____25236 -> begin
(

let uu____25238 = (

let uu____25244 = (

let uu____25246 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____25246))
in ((FStar_Errors.Fatal_UnexpectedImplictArgument), (uu____25244)))
in (

let uu____25250 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____25238 uu____25250)))
end))
end)));
))


let level_of_type_fail : 'Auu____25266 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  'Auu____25266 = (fun env e t -> (

let uu____25284 = (

let uu____25290 = (

let uu____25292 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____25292 t))
in ((FStar_Errors.Fatal_UnexpectedTermType), (uu____25290)))
in (

let uu____25296 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____25284 uu____25296))))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____25330 = (

let uu____25331 = (FStar_Syntax_Util.unrefine t1)
in uu____25331.FStar_Syntax_Syntax.n)
in (match (uu____25330) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____25335 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____25339 -> begin
(

let uu____25341 = (FStar_Syntax_Util.type_u ())
in (match (uu____25341) with
| (t_u, u) -> begin
(

let env1 = (

let uu___3344_25349 = env
in {FStar_TypeChecker_Env.solver = uu___3344_25349.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3344_25349.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3344_25349.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3344_25349.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3344_25349.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3344_25349.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3344_25349.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___3344_25349.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___3344_25349.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3344_25349.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3344_25349.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3344_25349.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3344_25349.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3344_25349.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3344_25349.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___3344_25349.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___3344_25349.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3344_25349.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3344_25349.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3344_25349.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___3344_25349.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3344_25349.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3344_25349.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3344_25349.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3344_25349.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3344_25349.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3344_25349.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3344_25349.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3344_25349.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___3344_25349.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3344_25349.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3344_25349.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3344_25349.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3344_25349.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3344_25349.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3344_25349.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3344_25349.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3344_25349.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3344_25349.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3344_25349.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3344_25349.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3344_25349.FStar_TypeChecker_Env.nbe})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____25354 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____25354))
end
| uu____25356 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun env e -> (

let uu____25373 = (

let uu____25374 = (FStar_Syntax_Subst.compress e)
in uu____25374.FStar_Syntax_Syntax.n)
in (match (uu____25373) with
| FStar_Syntax_Syntax.Tm_bvar (uu____25377) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____25380) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____25404) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____25421) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____25466) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____25473 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____25473) with
| ((uu____25482, t), uu____25484) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____25490 = (FStar_Syntax_Util.unfold_lazy i)
in (universe_of_aux env uu____25490))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____25493, (FStar_Util.Inl (t), uu____25495), uu____25496) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____25543, (FStar_Util.Inr (c), uu____25545), uu____25546) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____25594) -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant env e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____25603; FStar_Syntax_Syntax.vars = uu____25604}, us) -> begin
(

let uu____25610 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____25610) with
| ((us', t), uu____25621) -> begin
((match ((Prims.op_disEquality (FStar_List.length us) (FStar_List.length us'))) with
| true -> begin
(

let uu____25628 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), ("Unexpected number of universe instantiations")) uu____25628))
end
| uu____25631 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____25647 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____25649) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____25658) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____25685 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____25685) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____25705 -> (match (uu____25705) with
| (b, uu____25713) -> begin
(

let uu____25718 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____25718))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____25723 = (universe_of_aux env res)
in (level_of_type env res uu____25723)))
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
| FStar_Syntax_Syntax.Tm_bvar (uu____25834) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____25850) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____25888) -> begin
(

let uu____25889 = (universe_of_aux env hd3)
in ((uu____25889), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____25900) -> begin
(

let uu____25901 = (universe_of_aux env hd3)
in ((uu____25901), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____25912) -> begin
(

let uu____25925 = (universe_of_aux env hd3)
in ((uu____25925), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____25936) -> begin
(

let uu____25943 = (universe_of_aux env hd3)
in ((uu____25943), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____25954) -> begin
(

let uu____25981 = (universe_of_aux env hd3)
in ((uu____25981), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____25992) -> begin
(

let uu____25999 = (universe_of_aux env hd3)
in ((uu____25999), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____26010) -> begin
(

let uu____26011 = (universe_of_aux env hd3)
in ((uu____26011), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____26022) -> begin
(

let uu____26037 = (universe_of_aux env hd3)
in ((uu____26037), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____26048) -> begin
(

let uu____26055 = (universe_of_aux env hd3)
in ((uu____26055), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____26066) -> begin
(

let uu____26067 = (universe_of_aux env hd3)
in ((uu____26067), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____26078, (hd4)::uu____26080) -> begin
(

let uu____26145 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____26145) with
| (uu____26160, uu____26161, hd5) -> begin
(

let uu____26179 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____26179) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____26236 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env e)
in (

let uu____26238 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____26238) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____26296 -> begin
(

let uu____26297 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____26297) with
| (env1, uu____26319) -> begin
(

let env2 = (

let uu___3505_26325 = env1
in {FStar_TypeChecker_Env.solver = uu___3505_26325.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3505_26325.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3505_26325.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3505_26325.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3505_26325.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3505_26325.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3505_26325.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___3505_26325.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___3505_26325.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3505_26325.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3505_26325.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3505_26325.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3505_26325.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3505_26325.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3505_26325.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___3505_26325.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3505_26325.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3505_26325.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3505_26325.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___3505_26325.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3505_26325.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3505_26325.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3505_26325.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3505_26325.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3505_26325.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3505_26325.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3505_26325.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3505_26325.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3505_26325.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3505_26325.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3505_26325.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3505_26325.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3505_26325.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3505_26325.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3505_26325.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3505_26325.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3505_26325.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3505_26325.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3505_26325.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3505_26325.FStar_TypeChecker_Env.nbe})
in ((

let uu____26330 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____26330) with
| true -> begin
(

let uu____26335 = (

let uu____26337 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____26337))
in (

let uu____26338 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____26335 uu____26338)))
end
| uu____26341 -> begin
()
end));
(

let uu____26343 = (tc_term env2 hd3)
in (match (uu____26343) with
| (uu____26364, {FStar_Syntax_Syntax.eff_name = uu____26365; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____26367; FStar_Syntax_Syntax.comp_thunk = uu____26368}, g) -> begin
((

let uu____26382 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____26382 (fun a1 -> ())));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____26393 = (type_of_head true hd1 args)
in (match (uu____26393) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env t)
in (

let uu____26432 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____26432) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____26482 -> begin
(

let uu____26484 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____26484))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____26486, (hd1)::uu____26488) -> begin
(

let uu____26553 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____26553) with
| (uu____26554, uu____26555, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____26573, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____26620 = (universe_of_aux env e)
in (level_of_type env e uu____26620)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____26644 = (tc_binders env tps)
in (match (uu____26644) with
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
| FStar_Syntax_Syntax.Tm_delayed (uu____26702) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____26728) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____26734 = (FStar_Syntax_Util.unfold_lazy i)
in (type_of_well_typed_term env uu____26734))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____26736 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env [] fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____26736 (fun uu____26750 -> (match (uu____26750) with
| (t2, uu____26758) -> begin
FStar_Pervasives_Native.Some (t2)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____26760; FStar_Syntax_Syntax.vars = uu____26761}, us) -> begin
(

let uu____26767 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env us fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____26767 (fun uu____26781 -> (match (uu____26781) with
| (t2, uu____26789) -> begin
FStar_Pervasives_Native.Some (t2)
end))))
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____26790)) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(

let uu____26792 = (tc_constant env t1.FStar_Syntax_Syntax.pos sc)
in FStar_Pervasives_Native.Some (uu____26792))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____26794 = (mk_tm_type (FStar_Syntax_Syntax.U_succ (u)))
in FStar_Pervasives_Native.Some (uu____26794))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = eff; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (tbody); FStar_Syntax_Syntax.residual_flags = uu____26799})) -> begin
(

let mk_comp = (

let uu____26843 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____26843) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_Total')
end
| uu____26872 -> begin
(

let uu____26874 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____26874) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_GTotal')
end
| uu____26903 -> begin
FStar_Pervasives_Native.None
end))
end))
in (FStar_Util.bind_opt mk_comp (fun f -> (

let uu____26944 = (universe_of_well_typed_term env tbody)
in (FStar_Util.bind_opt uu____26944 (fun u -> (

let uu____26952 = (

let uu____26955 = (

let uu____26962 = (

let uu____26963 = (

let uu____26978 = (f tbody (FStar_Pervasives_Native.Some (u)))
in ((bs), (uu____26978)))
in FStar_Syntax_Syntax.Tm_arrow (uu____26963))
in (FStar_Syntax_Syntax.mk uu____26962))
in (uu____26955 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
in FStar_Pervasives_Native.Some (uu____26952))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____27015 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____27015) with
| (bs1, c1) -> begin
(

let rec aux = (fun env1 us bs2 -> (match (bs2) with
| [] -> begin
(

let uu____27074 = (universe_of_well_typed_term env1 (FStar_Syntax_Util.comp_result c1))
in (FStar_Util.bind_opt uu____27074 (fun uc -> (

let uu____27082 = (mk_tm_type (FStar_Syntax_Syntax.U_max ((uc)::us)))
in FStar_Pervasives_Native.Some (uu____27082)))))
end
| ((x, imp))::bs3 -> begin
(

let uu____27108 = (universe_of_well_typed_term env1 x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____27108 (fun u_x -> (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x)
in (aux env2 ((u_x)::us) bs3)))))
end))
in (aux env [] bs1))
end))
end
| FStar_Syntax_Syntax.Tm_abs (uu____27117) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____27137) -> begin
(

let uu____27142 = (universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____27142 (fun u_x -> (

let uu____27150 = (mk_tm_type u_x)
in FStar_Pervasives_Native.Some (uu____27150)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____27155; FStar_Syntax_Syntax.vars = uu____27156}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____27235 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____27235) with
| (unary_op1, uu____27255) -> begin
(

let head1 = (

let uu____27283 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____27283))
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (type_of_well_typed_term env t2)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____27331; FStar_Syntax_Syntax.vars = uu____27332}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____27428 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____27428) with
| (unary_op1, uu____27448) -> begin
(

let head1 = (

let uu____27476 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a1)::(a2)::[])))) FStar_Pervasives_Native.None uu____27476))
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (type_of_well_typed_term env t2)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____27532; FStar_Syntax_Syntax.vars = uu____27533}, (uu____27534)::[]) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.t_range)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____27573; FStar_Syntax_Syntax.vars = uu____27574}, ((t2, uu____27576))::(uu____27577)::[]) -> begin
(type_of_well_typed_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let t_hd = (type_of_well_typed_term env hd1)
in (

let rec aux = (fun t_hd1 -> (

let uu____27673 = (

let uu____27674 = (FStar_TypeChecker_Normalize.unfold_whnf env t_hd1)
in uu____27674.FStar_Syntax_Syntax.n)
in (match (uu____27673) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_bs = (FStar_List.length bs)
in (

let bs_t_opt = (match ((n_args < n_bs)) with
| true -> begin
(

let uu____27747 = (FStar_Util.first_N n_args bs)
in (match (uu____27747) with
| (bs1, rest) -> begin
(

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None t_hd1.FStar_Syntax_Syntax.pos)
in (

let uu____27835 = (

let uu____27840 = (FStar_Syntax_Syntax.mk_Total t2)
in (FStar_Syntax_Subst.open_comp bs1 uu____27840))
in (match (uu____27835) with
| (bs2, c1) -> begin
FStar_Pervasives_Native.Some (((bs2), ((FStar_Syntax_Util.comp_result c1))))
end)))
end))
end
| uu____27877 -> begin
(match ((Prims.op_Equality n_args n_bs)) with
| true -> begin
(

let uu____27894 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____27894) with
| (bs1, c1) -> begin
(

let uu____27915 = (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
in (match (uu____27915) with
| true -> begin
FStar_Pervasives_Native.Some (((bs1), ((FStar_Syntax_Util.comp_result c1))))
end
| uu____27952 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| uu____27966 -> begin
FStar_Pervasives_Native.None
end)
end)
in (FStar_Util.bind_opt bs_t_opt (fun uu____27997 -> (match (uu____27997) with
| (bs1, t2) -> begin
(

let subst1 = (FStar_List.map2 (fun b a -> FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), ((FStar_Pervasives_Native.fst a))))) bs1 args)
in (

let uu____28073 = (FStar_Syntax_Subst.subst subst1 t2)
in FStar_Pervasives_Native.Some (uu____28073)))
end))))))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____28075) -> begin
(aux x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____28081, uu____28082) -> begin
(aux t2)
end
| uu____28123 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_Util.bind_opt t_hd aux)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____28124, (FStar_Util.Inl (t2), uu____28126), uu____28127) -> begin
FStar_Pervasives_Native.Some (t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____28174, (FStar_Util.Inr (c), uu____28176), uu____28177) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____28242 = (FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
in FStar_Pervasives_Native.Some (uu____28242))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.t_term)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____28250) -> begin
(type_of_well_typed_term env t2)
end
| FStar_Syntax_Syntax.Tm_match (uu____28255) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____28278) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (uu____28292) -> begin
FStar_Pervasives_Native.None
end))))
and universe_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun env t -> (

let uu____28303 = (type_of_well_typed_term env t)
in (match (uu____28303) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.pos = uu____28309; FStar_Syntax_Syntax.vars = uu____28310}) -> begin
FStar_Pervasives_Native.Some (u)
end
| uu____28313 -> begin
FStar_Pervasives_Native.None
end)))


let check_type_of_well_typed_term' : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun must_total env t k -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let env2 = (

let uu___3784_28341 = env1
in {FStar_TypeChecker_Env.solver = uu___3784_28341.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3784_28341.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3784_28341.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3784_28341.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3784_28341.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3784_28341.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3784_28341.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___3784_28341.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___3784_28341.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3784_28341.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3784_28341.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3784_28341.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3784_28341.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3784_28341.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3784_28341.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___3784_28341.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___3784_28341.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3784_28341.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3784_28341.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3784_28341.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___3784_28341.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___3784_28341.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3784_28341.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3784_28341.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3784_28341.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3784_28341.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3784_28341.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3784_28341.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3784_28341.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3784_28341.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3784_28341.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3784_28341.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3784_28341.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3784_28341.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3784_28341.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3784_28341.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3784_28341.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3784_28341.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3784_28341.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3784_28341.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3784_28341.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3784_28341.FStar_TypeChecker_Env.nbe})
in (

let slow_check = (fun uu____28348 -> (match (must_total) with
| true -> begin
(

let uu____28350 = (env2.FStar_TypeChecker_Env.type_of env2 t)
in (match (uu____28350) with
| (uu____28357, uu____28358, g) -> begin
g
end))
end
| uu____28360 -> begin
(

let uu____28362 = (env2.FStar_TypeChecker_Env.tc_term env2 t)
in (match (uu____28362) with
| (uu____28369, uu____28370, g) -> begin
g
end))
end))
in (

let uu____28372 = (type_of_well_typed_term env2 t)
in (match (uu____28372) with
| FStar_Pervasives_Native.None -> begin
(slow_check ())
end
| FStar_Pervasives_Native.Some (k') -> begin
((

let uu____28377 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____28377) with
| true -> begin
(

let uu____28382 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____28384 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____28386 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____28388 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n" uu____28382 uu____28384 uu____28386 uu____28388)))))
end
| uu____28391 -> begin
()
end));
(

let g = (FStar_TypeChecker_Rel.subtype_nosmt env2 k' k)
in ((

let uu____28397 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____28397) with
| true -> begin
(

let uu____28402 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____28404 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____28406 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____28408 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n" uu____28402 (match ((FStar_Option.isSome g)) with
| true -> begin
"succeeded with guard"
end
| uu____28414 -> begin
"failed"
end) uu____28404 uu____28406 uu____28408)))))
end
| uu____28417 -> begin
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

let uu___3815_28445 = env1
in {FStar_TypeChecker_Env.solver = uu___3815_28445.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___3815_28445.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___3815_28445.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___3815_28445.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___3815_28445.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___3815_28445.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___3815_28445.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___3815_28445.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___3815_28445.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___3815_28445.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___3815_28445.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___3815_28445.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___3815_28445.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___3815_28445.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___3815_28445.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___3815_28445.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___3815_28445.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___3815_28445.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___3815_28445.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___3815_28445.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___3815_28445.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___3815_28445.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___3815_28445.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___3815_28445.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___3815_28445.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___3815_28445.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___3815_28445.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___3815_28445.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___3815_28445.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___3815_28445.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___3815_28445.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___3815_28445.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___3815_28445.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___3815_28445.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___3815_28445.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___3815_28445.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___3815_28445.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___3815_28445.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___3815_28445.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___3815_28445.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___3815_28445.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___3815_28445.FStar_TypeChecker_Env.nbe})
in (

let slow_check = (fun uu____28452 -> (match (must_total) with
| true -> begin
(

let uu____28454 = (env2.FStar_TypeChecker_Env.type_of env2 t)
in (match (uu____28454) with
| (uu____28461, uu____28462, g) -> begin
g
end))
end
| uu____28464 -> begin
(

let uu____28466 = (env2.FStar_TypeChecker_Env.tc_term env2 t)
in (match (uu____28466) with
| (uu____28473, uu____28474, g) -> begin
g
end))
end))
in (

let uu____28476 = (

let uu____28478 = (FStar_Options.__temp_fast_implicits ())
in (FStar_All.pipe_left Prims.op_Negation uu____28478))
in (match (uu____28476) with
| true -> begin
(slow_check ())
end
| uu____28483 -> begin
(check_type_of_well_typed_term' must_total env2 t k)
end))))))




