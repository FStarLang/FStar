
open Prims
open FStar_Pervasives

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___69_4 = env
in {FStar_TypeChecker_Env.solver = uu___69_4.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___69_4.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___69_4.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___69_4.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___69_4.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___69_4.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___69_4.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___69_4.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___69_4.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___69_4.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___69_4.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___69_4.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___69_4.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___69_4.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___69_4.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___69_4.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___69_4.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___69_4.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___69_4.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___69_4.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___69_4.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___69_4.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___69_4.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___69_4.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___69_4.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___69_4.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___69_4.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___69_4.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___69_4.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___69_4.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___69_4.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___69_4.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___69_4.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___69_4.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___69_4.FStar_TypeChecker_Env.dep_graph}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___70_8 = env
in {FStar_TypeChecker_Env.solver = uu___70_8.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___70_8.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___70_8.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___70_8.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___70_8.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___70_8.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___70_8.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___70_8.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___70_8.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___70_8.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___70_8.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___70_8.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___70_8.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___70_8.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___70_8.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___70_8.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___70_8.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___70_8.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___70_8.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___70_8.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___70_8.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___70_8.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___70_8.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___70_8.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___70_8.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___70_8.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___70_8.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___70_8.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___70_8.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___70_8.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___70_8.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___70_8.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___70_8.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___70_8.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___70_8.FStar_TypeChecker_Env.dep_graph}))


let mk_lex_list : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v1 tl1 -> (

let r = (match ((Prims.op_Equality tl1.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
v1.FStar_Syntax_Syntax.pos
end
| uu____39 -> begin
(FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos tl1.FStar_Syntax_Syntax.pos)
end)
in (

let uu____40 = (

let uu____41 = (

let uu____42 = (FStar_Syntax_Syntax.as_arg v1)
in (

let uu____43 = (

let uu____46 = (FStar_Syntax_Syntax.as_arg tl1)
in (uu____46)::[])
in (uu____42)::uu____43))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____41))
in (uu____40 FStar_Pervasives_Native.None r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___64_53 -> (match (uu___64_53) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____56 -> begin
false
end))


let steps : 'Auu____61 . 'Auu____61  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[])


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
t
end
| uu____107 -> begin
(

let t1 = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____111 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t1)
in (

let uu____115 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____115) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t1)
end
| uu____121 -> begin
(

let fail1 = (fun uu____125 -> (

let msg = (match (head_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____127 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" uu____127))
end
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____129 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____130 = (FStar_TypeChecker_Normalize.term_to_string env head1)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" uu____129 uu____130)))
end)
in (

let uu____131 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_EscapedBoundVar), (msg)) uu____131))))
in (

let s = (

let uu____133 = (

let uu____134 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____134))
in (FStar_TypeChecker_Util.new_uvar env uu____133))
in (

let uu____143 = (FStar_TypeChecker_Rel.try_teq true env t1 s)
in (match (uu____143) with
| FStar_Pervasives_Native.Some (g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
s;
)
end
| uu____148 -> begin
(fail1 ())
end))))
end)
end))))
end))
in (aux false kt)))


let push_binding : 'Auu____154 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____154)  ->  FStar_TypeChecker_Env.env = (fun env b -> (FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v1 -> (

let uu____184 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____184) with
| true -> begin
s
end
| uu____185 -> begin
(FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), (v1))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags (fun uu____196 -> (

let uu____197 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Util.set_result_typ uu____197 t)))))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> e)


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____240 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____240))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____249 = (

let uu____256 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____256) with
| FStar_Pervasives_Native.None -> begin
(((memo_tk e t)), (lc), (guard))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____266 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_prop env e lc t')
in (match (uu____266) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____282 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____282) with
| (e2, g) -> begin
((

let uu____296 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____296) with
| true -> begin
(

let uu____297 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____298 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____299 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____300 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____297 uu____298 uu____299 uu____300)))))
end
| uu____301 -> begin
()
end));
(

let msg = (

let uu____307 = (FStar_TypeChecker_Rel.is_trivial g)
in (match (uu____307) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____314 -> begin
(FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____324 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc1 g1)
in (match (uu____324) with
| (lc2, g2) -> begin
(

let uu____337 = (set_lcomp_result lc2 t')
in (((memo_tk e2 t')), (uu____337), (g2)))
end))));
)
end)))
end))
end))
in (match (uu____249) with
| (e1, lc1, g) -> begin
((e1), (lc1), (g))
end)))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____368 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____368) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____378 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_prop env e lc t)
in (match (uu____378) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt ec -> (

let uu____424 = ec
in (match (uu____424) with
| (e, c) -> begin
(

let tot_or_gtot = (fun c1 -> (

let uu____445 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____445) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c1))
end
| uu____446 -> begin
(

let uu____447 = (FStar_Syntax_Util.is_pure_or_ghost_comp c1)
in (match (uu____447) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c1))
end
| uu____448 -> begin
(failwith "Impossible: Expected pure_or_ghost comp")
end))
end)))
in (

let uu____449 = (match (copt) with
| FStar_Pervasives_Native.Some (uu____462) -> begin
((copt), (c))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____465 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Parser_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____467 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____467)))))
in (match (uu____465) with
| true -> begin
(

let uu____474 = (

let uu____477 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____477))
in ((uu____474), (c)))
end
| uu____480 -> begin
(

let uu____481 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____481) with
| true -> begin
(

let uu____488 = (tot_or_gtot c)
in ((FStar_Pervasives_Native.None), (uu____488)))
end
| uu____491 -> begin
(

let uu____492 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____492) with
| true -> begin
(

let uu____499 = (

let uu____502 = (tot_or_gtot c)
in FStar_Pervasives_Native.Some (uu____502))
in ((uu____499), (c)))
end
| uu____505 -> begin
((FStar_Pervasives_Native.None), (c))
end))
end))
end))
end)
in (match (uu____449) with
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

let uu____529 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e uu____529))
in (

let c4 = (FStar_Syntax_Syntax.lcomp_comp c3)
in (

let uu____531 = (FStar_TypeChecker_Util.check_comp env e c4 expected_c)
in (match (uu____531) with
| (e1, uu____545, g) -> begin
(

let g1 = (

let uu____548 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____548 "could not prove post-condition" g))
in ((

let uu____550 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____550) with
| true -> begin
(

let uu____551 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____552 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" uu____551 uu____552)))
end
| uu____553 -> begin
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


let no_logical_guard : 'Auu____559 'Auu____560 . FStar_TypeChecker_Env.env  ->  ('Auu____559 * 'Auu____560 * FStar_TypeChecker_Env.guard_t)  ->  ('Auu____559 * 'Auu____560 * FStar_TypeChecker_Env.guard_t) = (fun env uu____580 -> (match (uu____580) with
| (te, kt, f) -> begin
(

let uu____590 = (FStar_TypeChecker_Rel.guard_form f)
in (match (uu____590) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____598 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____603 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____598 uu____603)))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let uu____613 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____613) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "Expected type is None\n")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____617 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____617))
end)))


let rec get_pat_vars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun pats acc -> (

let pats1 = (FStar_Syntax_Util.unmeta pats)
in (

let uu____641 = (FStar_Syntax_Util.head_and_args pats1)
in (match (uu____641) with
| (head1, args) -> begin
(

let uu____680 = (

let uu____681 = (FStar_Syntax_Util.un_uinst head1)
in uu____681.FStar_Syntax_Syntax.n)
in (match (uu____680) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
acc
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
(

let uu____688 = (FStar_List.tl args)
in (get_pat_vars_args uu____688 acc))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
(get_pat_vars_args args acc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(get_pat_vars_args args acc)
end
| uu____697 -> begin
(

let uu____698 = (FStar_Syntax_Free.names pats1)
in (FStar_Util.set_union acc uu____698))
end))
end))))
and get_pat_vars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun args acc -> (FStar_List.fold_left (fun s arg -> (get_pat_vars (FStar_Pervasives_Native.fst arg) s)) acc args))


let check_smt_pat : 'Auu____728 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * 'Auu____728) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.unit = (fun env t bs c -> (

let uu____761 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____761) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____762; FStar_Syntax_Syntax.effect_name = uu____763; FStar_Syntax_Syntax.result_typ = uu____764; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____768))::[]; FStar_Syntax_Syntax.flags = uu____769}) -> begin
(

let pat_vars = (

let uu____817 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (

let uu____818 = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
in (get_pat_vars uu____817 uu____818)))
in (

let uu____821 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____848 -> (match (uu____848) with
| (b, uu____854) -> begin
(

let uu____855 = (FStar_Util.set_mem b pat_vars)
in (not (uu____855)))
end))))
in (match (uu____821) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____861) -> begin
(

let uu____866 = (

let uu____871 = (

let uu____872 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____872))
in ((FStar_Errors.Warning_PatternMissingBoundVar), (uu____871)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____866))
end)))
end
| uu____873 -> begin
(failwith "Impossible")
end)
end
| uu____874 -> begin
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

let uu___71_923 = env
in {FStar_TypeChecker_Env.solver = uu___71_923.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___71_923.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___71_923.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___71_923.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___71_923.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___71_923.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___71_923.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___71_923.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___71_923.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___71_923.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___71_923.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___71_923.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___71_923.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___71_923.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___71_923.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___71_923.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___71_923.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___71_923.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___71_923.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___71_923.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___71_923.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___71_923.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___71_923.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___71_923.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___71_923.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___71_923.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___71_923.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___71_923.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___71_923.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___71_923.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___71_923.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___71_923.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___71_923.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___71_923.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___71_923.FStar_TypeChecker_Env.dep_graph})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> ((

let uu____939 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____939) with
| true -> begin
(

let uu____940 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (

let uu____941 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "Building a decreases clause over (%s) and %s\n" uu____940 uu____941)))
end
| uu____942 -> begin
()
end));
(

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____960 -> (match (uu____960) with
| (b, uu____968) -> begin
(

let t = (

let uu____970 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____970))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____973) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____974) -> begin
[]
end
| uu____987 -> begin
(

let uu____988 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____988)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____993 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____993) with
| (head1, uu____1009) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____1031 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____1035 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___65_1044 -> (match (uu___65_1044) with
| FStar_Syntax_Syntax.DECREASES (uu____1045) -> begin
true
end
| uu____1048 -> begin
false
end))))
in (match (uu____1035) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____1052 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____1061 -> begin
(mk_lex_list xs)
end))
end)))));
))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____1082 -> (match (uu____1082) with
| (l, t, u_names) -> begin
(

let uu____1100 = (

let uu____1101 = (FStar_Syntax_Subst.compress t)
in uu____1101.FStar_Syntax_Syntax.n)
in (match (uu____1100) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____1162 -> (match (uu____1162) with
| (x, imp) -> begin
(

let uu____1173 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____1173) with
| true -> begin
(

let uu____1178 = (

let uu____1179 = (

let uu____1182 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____1182))
in (FStar_Syntax_Syntax.new_bv uu____1179 x.FStar_Syntax_Syntax.sort))
in ((uu____1178), (imp)))
end
| uu____1183 -> begin
((x), (imp))
end))
end))))
in (

let uu____1184 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____1184) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____1203 = (

let uu____1204 = (

let uu____1205 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____1206 = (

let uu____1209 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____1209)::[])
in (uu____1205)::uu____1206))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____1204))
in (uu____1203 FStar_Pervasives_Native.None r))
in (

let uu____1212 = (FStar_Util.prefix formals2)
in (match (uu____1212) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___72_1259 = last1
in (

let uu____1260 = (FStar_Syntax_Util.refine last1 precedes1)
in {FStar_Syntax_Syntax.ppname = uu___72_1259.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___72_1259.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1260}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____1286 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1286) with
| true -> begin
(

let uu____1287 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____1288 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1289 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____1287 uu____1288 uu____1289))))
end
| uu____1290 -> begin
()
end));
((l), (t'), (u_names));
))))
end))))
end)))
end
| uu____1293 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectedArrowAnnotatedType), ("Annotated type of \'let rec\' must be an arrow")) t.FStar_Syntax_Syntax.pos)
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let uu___73_1744 = env
in {FStar_TypeChecker_Env.solver = uu___73_1744.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___73_1744.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___73_1744.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___73_1744.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___73_1744.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___73_1744.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___73_1744.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___73_1744.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___73_1744.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___73_1744.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___73_1744.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___73_1744.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___73_1744.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___73_1744.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___73_1744.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___73_1744.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___73_1744.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___73_1744.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___73_1744.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___73_1744.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___73_1744.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___73_1744.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___73_1744.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___73_1744.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___73_1744.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___73_1744.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___73_1744.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___73_1744.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___73_1744.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___73_1744.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___73_1744.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___73_1744.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___73_1744.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___73_1744.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___73_1744.FStar_TypeChecker_Env.dep_graph}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (match ((Prims.op_Equality e.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____1754 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____1756 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1756) with
| true -> begin
(

let uu____1757 = (

let uu____1758 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1758))
in (

let uu____1759 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" uu____1757 uu____1759)))
end
| uu____1760 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1768) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1799) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1806) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1823) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____1824) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1825) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1826) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____1827) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1844) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____1857) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____1864) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1865, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aqs}) when (FStar_List.for_all (fun uu____1893 -> (match (uu____1893) with
| (uu____1902, b, uu____1904) -> begin
(not (b))
end)) aqs) -> begin
(value_check_expected_typ env1 top (FStar_Util.Inl (FStar_Syntax_Syntax.t_term)) FStar_TypeChecker_Rel.trivial_guard)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1909) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Tac_lid; FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_term; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.SOMETRIVIAL)::(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]})
in (

let uu____1923 = (

let uu____1930 = (

let uu____1935 = (FStar_Syntax_Util.lcomp_of_comp c)
in FStar_Util.Inr (uu____1935))
in (value_check_expected_typ env1 top uu____1930 FStar_TypeChecker_Rel.trivial_guard))
in (match (uu____1923) with
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

let uu____1958 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____1958) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___74_1975 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___74_1975.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___74_1975.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___74_1975.FStar_TypeChecker_Env.implicits})
in (

let uu____1976 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____1976), (c), (g1))))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____1997 = (FStar_Syntax_Util.type_u ())
in (match (uu____1997) with
| (t, u) -> begin
(

let uu____2010 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____2010) with
| (e2, c, g) -> begin
(

let uu____2026 = (

let uu____2041 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2041) with
| (env2, uu____2063) -> begin
(tc_pats env2 pats)
end))
in (match (uu____2026) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___75_2097 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___75_2097.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___75_2097.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___75_2097.FStar_TypeChecker_Env.implicits})
in (

let uu____2098 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2101 = (FStar_TypeChecker_Rel.conj_guard g g'1)
in ((uu____2098), (c), (uu____2101)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____2109 = (

let uu____2110 = (FStar_Syntax_Subst.compress e1)
in uu____2110.FStar_Syntax_Syntax.n)
in (match (uu____2109) with
| FStar_Syntax_Syntax.Tm_let ((uu____2119, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____2121; FStar_Syntax_Syntax.lbtyp = uu____2122; FStar_Syntax_Syntax.lbeff = uu____2123; FStar_Syntax_Syntax.lbdef = e11; FStar_Syntax_Syntax.lbattrs = uu____2125; FStar_Syntax_Syntax.lbpos = uu____2126})::[]), e2) -> begin
(

let uu____2154 = (

let uu____2161 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (tc_term uu____2161 e11))
in (match (uu____2154) with
| (e12, c1, g1) -> begin
(

let uu____2171 = (tc_term env1 e2)
in (match (uu____2171) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.maybe_return_e2_and_bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 e21 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e3 = (

let uu____2195 = (

let uu____2198 = (

let uu____2199 = (

let uu____2212 = (

let uu____2219 = (

let uu____2222 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_Syntax_Syntax.t_unit), (e13), (e13.FStar_Syntax_Syntax.pos)))
in (uu____2222)::[])
in ((false), (uu____2219)))
in ((uu____2212), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____2199))
in (FStar_Syntax_Syntax.mk uu____2198))
in (uu____2195 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2244 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e5), (c), (uu____2244)))))))))
end))
end))
end
| uu____2247 -> begin
(

let uu____2248 = (tc_term env1 e1)
in (match (uu____2248) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____2270)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic_lift (uu____2282)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____2301 = (tc_term env1 e1)
in (match (uu____2301) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____2325) -> begin
(

let uu____2372 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2372) with
| (env0, uu____2386) -> begin
(

let uu____2391 = (tc_comp env0 expected_c)
in (match (uu____2391) with
| (expected_c1, uu____2405, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c1)
in (

let uu____2410 = (

let uu____2417 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____2417 e1))
in (match (uu____2410) with
| (e2, c', g') -> begin
(

let uu____2427 = (

let uu____2434 = (

let uu____2439 = (FStar_Syntax_Syntax.lcomp_comp c')
in ((e2), (uu____2439)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____2434))
in (match (uu____2427) with
| (e3, expected_c2, g'') -> begin
(

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inr (expected_c2)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____2484 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____2484))
in (

let topt1 = (tc_tactic_opt env0 topt)
in (

let f1 = (match (topt1) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(FStar_TypeChecker_Rel.map_guard f (fun f1 -> (

let uu____2493 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero f1)
in (FStar_TypeChecker_Common.mk_by_tactic tactic uu____2493))))
end)
in (

let uu____2494 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____2494) with
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
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____2514) -> begin
(

let uu____2561 = (FStar_Syntax_Util.type_u ())
in (match (uu____2561) with
| (k, u) -> begin
(

let uu____2574 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____2574) with
| (t1, uu____2588, f) -> begin
(

let uu____2590 = (

let uu____2597 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____2597 e1))
in (match (uu____2590) with
| (e2, c, g) -> begin
(

let uu____2607 = (

let uu____2612 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____2616 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____2612 e2 c f))
in (match (uu____2607) with
| (c1, f1) -> begin
(

let uu____2625 = (

let uu____2632 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____2632 c1))
in (match (uu____2625) with
| (e3, c2, f2) -> begin
(

let uu____2672 = (

let uu____2673 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____2673))
in ((e3), (c2), (uu____2672)))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____2674; FStar_Syntax_Syntax.vars = uu____2675}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____2738 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2738) with
| (unary_op, uu____2760) -> begin
(

let head1 = (

let uu____2784 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____2784))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____2822; FStar_Syntax_Syntax.vars = uu____2823}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____2886 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2886) with
| (unary_op, uu____2908) -> begin
(

let head1 = (

let uu____2932 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____2932))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____2970)); FStar_Syntax_Syntax.pos = uu____2971; FStar_Syntax_Syntax.vars = uu____2972}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3035 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3035) with
| (unary_op, uu____3057) -> begin
(

let head1 = (

let uu____3081 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____3081))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____3119; FStar_Syntax_Syntax.vars = uu____3120}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3196 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3196) with
| (unary_op, uu____3218) -> begin
(

let head1 = (

let uu____3242 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a1)::(a2)::[])))) FStar_Pervasives_Native.None uu____3242))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____3286; FStar_Syntax_Syntax.vars = uu____3287}, ((e1, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____3325 = (

let uu____3332 = (

let uu____3333 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3333))
in (tc_term uu____3332 e1))
in (match (uu____3325) with
| (e2, c, g) -> begin
(

let uu____3357 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3357) with
| (head1, uu____3379) -> begin
(

let uu____3400 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((((e2), (FStar_Pervasives_Native.None)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3427 = (

let uu____3428 = (

let uu____3431 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_Syntax_Syntax.mk_Total uu____3431))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3428))
in ((uu____3400), (uu____3427), (g))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____3436; FStar_Syntax_Syntax.vars = uu____3437}, ((t, FStar_Pervasives_Native.None))::((r, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____3490 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3490) with
| (head1, uu____3512) -> begin
(

let env' = (

let uu____3534 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_TypeChecker_Env.set_expected_typ env1 uu____3534))
in (

let uu____3535 = (tc_term env' r)
in (match (uu____3535) with
| (er, uu____3549, gr) -> begin
(

let uu____3551 = (tc_term env1 t)
in (match (uu____3551) with
| (t1, tt, gt1) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard gr gt1)
in (

let uu____3568 = (

let uu____3571 = (

let uu____3572 = (

let uu____3573 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3574 = (

let uu____3577 = (FStar_Syntax_Syntax.as_arg r)
in (uu____3577)::[])
in (uu____3573)::uu____3574))
in (FStar_Syntax_Syntax.mk_Tm_app head1 uu____3572))
in (uu____3571 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in ((uu____3568), (tt), (g))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____3582; FStar_Syntax_Syntax.vars = uu____3583}, uu____3584) -> begin
(

let uu____3605 = (

let uu____3610 = (

let uu____3611 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____3611))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____3610)))
in (FStar_Errors.raise_error uu____3605 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____3618; FStar_Syntax_Syntax.vars = uu____3619}, uu____3620) -> begin
(

let uu____3641 = (

let uu____3646 = (

let uu____3647 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____3647))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____3646)))
in (FStar_Errors.raise_error uu____3641 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____3654; FStar_Syntax_Syntax.vars = uu____3655}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify), ("Qualifier on argument to reify is irrelevant and will be ignored")))
end
| uu____3687 -> begin
()
end);
(

let uu____3688 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3688) with
| (env0, uu____3702) -> begin
(

let uu____3707 = (tc_term env0 e1)
in (match (uu____3707) with
| (e2, c, g) -> begin
(

let uu____3723 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3723) with
| (reify_op, uu____3745) -> begin
(

let u_c = (

let uu____3767 = (tc_term env0 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____3767) with
| (uu____3774, c', uu____3776) -> begin
(

let uu____3777 = (

let uu____3778 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____3778.FStar_Syntax_Syntax.n)
in (match (uu____3777) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____3782 -> begin
(

let uu____3783 = (FStar_Syntax_Util.type_u ())
in (match (uu____3783) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3795 = (

let uu____3796 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____3797 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____3798 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____3796 uu____3797 uu____3798))))
in (failwith uu____3795))
end);
u;
))
end))
end))
end))
in (

let repr = (

let uu____3800 = (FStar_Syntax_Syntax.lcomp_comp c)
in (FStar_TypeChecker_Env.reify_comp env1 uu____3800 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____3821 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____3821 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____3822 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____3822) with
| (e4, c2, g') -> begin
(

let uu____3838 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e4), (c2), (uu____3838)))
end))))))
end))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.pos = uu____3840; FStar_Syntax_Syntax.vars = uu____3841}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect), ("Qualifier on argument to reflect is irrelevant and will be ignored")))
end
| uu____3873 -> begin
()
end);
(

let no_reflect = (fun uu____3883 -> (

let uu____3884 = (

let uu____3889 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____3889)))
in (FStar_Errors.raise_error uu____3884 e1.FStar_Syntax_Syntax.pos)))
in (

let uu____3896 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3896) with
| (reflect_op, uu____3918) -> begin
(

let uu____3939 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____3939) with
| FStar_Pervasives_Native.None -> begin
(no_reflect ())
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____3972 = (

let uu____3973 = (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____3973)))
in (match (uu____3972) with
| true -> begin
(no_reflect ())
end
| uu____3982 -> begin
(

let uu____3983 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3983) with
| (env_no_ex, topt) -> begin
(

let uu____4002 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____4022 = (

let uu____4025 = (

let uu____4026 = (

let uu____4041 = (

let uu____4044 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____4045 = (

let uu____4048 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____4048)::[])
in (uu____4044)::uu____4045))
in ((repr), (uu____4041)))
in FStar_Syntax_Syntax.Tm_app (uu____4026))
in (FStar_Syntax_Syntax.mk uu____4025))
in (uu____4022 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____4054 = (

let uu____4061 = (

let uu____4062 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____4062 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____4061 t))
in (match (uu____4054) with
| (t1, uu____4090, g) -> begin
(

let uu____4092 = (

let uu____4093 = (FStar_Syntax_Subst.compress t1)
in uu____4093.FStar_Syntax_Syntax.n)
in (match (uu____4092) with
| FStar_Syntax_Syntax.Tm_app (uu____4108, ((res, uu____4110))::((wp, uu____4112))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____4155 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____4002) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____4186 = (

let uu____4191 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____4191) with
| (e2, c, g) -> begin
((

let uu____4206 = (

let uu____4207 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____4207))
in (match (uu____4206) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 ((((FStar_Errors.Error_UnexpectedGTotComputation), ("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____4220 -> begin
()
end));
(

let uu____4221 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____4221) with
| FStar_Pervasives_Native.None -> begin
((

let uu____4229 = (

let uu____4238 = (

let uu____4245 = (

let uu____4246 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____4247 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____4246 uu____4247)))
in ((FStar_Errors.Error_UnexpectedInstance), (uu____4245), (e2.FStar_Syntax_Syntax.pos)))
in (uu____4238)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____4229));
(

let uu____4260 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e2), (uu____4260)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____4262 = (

let uu____4263 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____4263))
in ((e2), (uu____4262)))
end));
)
end))
in (match (uu____4186) with
| (e2, g) -> begin
(

let c = (

let uu____4273 = (

let uu____4274 = (

let uu____4275 = (

let uu____4276 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____4276)::[])
in (

let uu____4277 = (

let uu____4286 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4286)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____4275; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____4277; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____4274))
in (FStar_All.pipe_right uu____4273 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____4306 = (comp_check_expected_typ env1 e3 c)
in (match (uu____4306) with
| (e4, c1, g') -> begin
(

let uu____4322 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e4), (c1), (uu____4322)))
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

let uu____4369 = (

let uu____4370 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____4370 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____4369 instantiate_both))
in ((

let uu____4386 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____4386) with
| true -> begin
(

let uu____4387 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____4388 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____4387 uu____4388)))
end
| uu____4389 -> begin
()
end));
(

let uu____4390 = (tc_term (no_inst env2) head1)
in (match (uu____4390) with
| (head2, chead, g_head) -> begin
(

let uu____4406 = (

let uu____4413 = ((not (env2.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____4413) with
| true -> begin
(

let uu____4420 = (

let uu____4427 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____4427))
in (match (uu____4420) with
| (e1, c, g) -> begin
((e1), (c), (g))
end))
end
| uu____4439 -> begin
(

let uu____4440 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env2 head2 chead g_head args uu____4440))
end))
in (match (uu____4406) with
| (e1, c, g) -> begin
((

let uu____4453 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____4453) with
| true -> begin
(

let uu____4454 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____4454))
end
| uu____4455 -> begin
()
end));
(

let uu____4456 = (comp_check_expected_typ env0 e1 c)
in (match (uu____4456) with
| (e2, c1, g') -> begin
(

let gimp = (

let uu____4473 = (

let uu____4474 = (FStar_Syntax_Subst.compress head2)
in uu____4474.FStar_Syntax_Syntax.n)
in (match (uu____4473) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____4478) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e2), (c1.FStar_Syntax_Syntax.res_typ), (head2.FStar_Syntax_Syntax.pos))
in (

let uu___76_4540 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___76_4540.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___76_4540.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___76_4540.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____4589 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (

let uu____4591 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g uu____4591))
in ((

let uu____4593 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____4593) with
| true -> begin
(

let uu____4594 = (FStar_Syntax_Print.term_to_string e2)
in (

let uu____4595 = (FStar_TypeChecker_Rel.guard_to_string env2 gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____4594 uu____4595)))
end
| uu____4596 -> begin
()
end));
((e2), (c1), (gres));
)))
end));
)
end))
end));
)))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let uu____4635 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____4635) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____4655 = (tc_term env12 e1)
in (match (uu____4655) with
| (e11, c1, g1) -> begin
(

let uu____4671 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4681 = (FStar_Syntax_Util.type_u ())
in (match (uu____4681) with
| (k, uu____4691) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env1 k)
in (

let uu____4693 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in ((uu____4693), (res_t))))
end))
end)
in (match (uu____4671) with
| (env_branches, res_t) -> begin
((

let uu____4703 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____4703) with
| true -> begin
(

let uu____4704 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____4704))
end
| uu____4705 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____4814 = (

let uu____4819 = (FStar_List.fold_right (fun uu____4891 uu____4892 -> (match (((uu____4891), (uu____4892))) with
| ((branch1, f, eff_label, cflags, c, g), (caccum, gaccum)) -> begin
(

let uu____5097 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (eff_label), (cflags), (c)))::caccum), (uu____5097)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____4819) with
| (cases, g) -> begin
(

let uu____5188 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____5188), (g)))
end))
in (match (uu____4814) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____5302 -> (match (uu____5302) with
| ((pat, wopt, br), uu____5338, eff_label, uu____5340, uu____5341, uu____5342) -> begin
(

let uu____5363 = (FStar_TypeChecker_Util.maybe_lift env1 br eff_label cres.FStar_Syntax_Syntax.eff_name res_t)
in ((pat), (wopt), (uu____5363)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____5418 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____5418) with
| true -> begin
(mk_match e11)
end
| uu____5421 -> begin
(

let e_match = (

let uu____5425 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____5425))
in (

let lb = (

let uu____5429 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (guard_x)) [] c1.FStar_Syntax_Syntax.res_typ uu____5429 e11 [] e11.FStar_Syntax_Syntax.pos))
in (

let e2 = (

let uu____5435 = (

let uu____5438 = (

let uu____5439 = (

let uu____5452 = (

let uu____5453 = (

let uu____5454 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____5454)::[])
in (FStar_Syntax_Subst.close uu____5453 e_match))
in ((((false), ((lb)::[]))), (uu____5452)))
in FStar_Syntax_Syntax.Tm_let (uu____5439))
in (FStar_Syntax_Syntax.mk uu____5438))
in (uu____5435 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____5467 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____5467) with
| true -> begin
(

let uu____5468 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____5469 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____5468 uu____5469)))
end
| uu____5470 -> begin
()
end));
(

let uu____5471 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e2), (cres), (uu____5471)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____5474); FStar_Syntax_Syntax.lbunivs = uu____5475; FStar_Syntax_Syntax.lbtyp = uu____5476; FStar_Syntax_Syntax.lbeff = uu____5477; FStar_Syntax_Syntax.lbdef = uu____5478; FStar_Syntax_Syntax.lbattrs = uu____5479; FStar_Syntax_Syntax.lbpos = uu____5480})::[]), uu____5481) -> begin
((

let uu____5505 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____5505) with
| true -> begin
(

let uu____5506 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____5506))
end
| uu____5507 -> begin
()
end));
(

let uu____5508 = (FStar_Options.use_two_phase_tc ())
in (match (uu____5508) with
| true -> begin
(

let is_lb_unannotated = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((uu____5519, (lb)::[]), uu____5521) -> begin
(

let uu____5534 = (

let uu____5535 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in uu____5535.FStar_Syntax_Syntax.n)
in (Prims.op_Equality uu____5534 FStar_Syntax_Syntax.Tm_unknown))
end
| uu____5538 -> begin
(failwith "Impossible")
end))
in (

let drop_lbtyp = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((t1, (lb)::[]), t2) -> begin
(

let uu___77_5558 = t
in (

let uu____5559 = (

let uu____5560 = (

let uu____5573 = (

let uu____5580 = (

let uu____5583 = (

let uu___78_5584 = lb
in (

let uu____5585 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.pos)
in {FStar_Syntax_Syntax.lbname = uu___78_5584.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___78_5584.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5585; FStar_Syntax_Syntax.lbeff = uu___78_5584.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___78_5584.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___78_5584.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___78_5584.FStar_Syntax_Syntax.lbpos}))
in (uu____5583)::[])
in ((t1), (uu____5580)))
in ((uu____5573), (t2)))
in FStar_Syntax_Syntax.Tm_let (uu____5560))
in {FStar_Syntax_Syntax.n = uu____5559; FStar_Syntax_Syntax.pos = uu___77_5558.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___77_5558.FStar_Syntax_Syntax.vars}))
end
| uu____5598 -> begin
(failwith "Impossible")
end))
in (

let uu____5599 = (check_top_level_let (

let uu___79_5608 = env1
in {FStar_TypeChecker_Env.solver = uu___79_5608.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___79_5608.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___79_5608.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___79_5608.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___79_5608.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___79_5608.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___79_5608.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___79_5608.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___79_5608.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___79_5608.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___79_5608.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___79_5608.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___79_5608.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___79_5608.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___79_5608.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___79_5608.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___79_5608.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___79_5608.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___79_5608.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___79_5608.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___79_5608.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___79_5608.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___79_5608.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___79_5608.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___79_5608.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___79_5608.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___79_5608.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___79_5608.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___79_5608.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___79_5608.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___79_5608.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___79_5608.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___79_5608.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___79_5608.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___79_5608.FStar_TypeChecker_Env.dep_graph}) top)
in (match (uu____5599) with
| (lax_top, l, g) -> begin
(

let lax_top1 = (FStar_TypeChecker_Normalize.remove_uvar_solutions env1 lax_top)
in ((

let uu____5620 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____5620) with
| true -> begin
(

let uu____5621 = (FStar_Syntax_Print.term_to_string lax_top1)
in (FStar_Util.print1 "Phase 1: checked %s\n" uu____5621))
end
| uu____5622 -> begin
()
end));
(

let uu____5623 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5623) with
| true -> begin
(

let uu____5630 = (

let uu____5631 = (is_lb_unannotated top)
in (match (uu____5631) with
| true -> begin
(drop_lbtyp lax_top1)
end
| uu____5632 -> begin
lax_top1
end))
in (check_top_level_let env1 uu____5630))
end
| uu____5633 -> begin
((lax_top1), (l), (g))
end));
))
end))))
end
| uu____5634 -> begin
(check_top_level_let env1 top)
end));
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____5635), uu____5636) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____5651); FStar_Syntax_Syntax.lbunivs = uu____5652; FStar_Syntax_Syntax.lbtyp = uu____5653; FStar_Syntax_Syntax.lbeff = uu____5654; FStar_Syntax_Syntax.lbdef = uu____5655; FStar_Syntax_Syntax.lbattrs = uu____5656; FStar_Syntax_Syntax.lbpos = uu____5657})::uu____5658), uu____5659) -> begin
((

let uu____5685 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____5685) with
| true -> begin
(

let uu____5686 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____5686))
end
| uu____5687 -> begin
()
end));
(

let uu____5688 = (FStar_Options.use_two_phase_tc ())
in (match (uu____5688) with
| true -> begin
(

let uu____5695 = (check_top_level_let_rec (

let uu___80_5704 = env1
in {FStar_TypeChecker_Env.solver = uu___80_5704.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___80_5704.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___80_5704.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___80_5704.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___80_5704.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___80_5704.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___80_5704.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___80_5704.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___80_5704.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___80_5704.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___80_5704.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___80_5704.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___80_5704.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___80_5704.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___80_5704.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___80_5704.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___80_5704.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___80_5704.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___80_5704.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___80_5704.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___80_5704.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___80_5704.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___80_5704.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___80_5704.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___80_5704.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___80_5704.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___80_5704.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___80_5704.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___80_5704.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___80_5704.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___80_5704.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___80_5704.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___80_5704.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___80_5704.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___80_5704.FStar_TypeChecker_Env.dep_graph}) top)
in (match (uu____5695) with
| (lax_top, l, g) -> begin
(

let lax_top1 = (FStar_TypeChecker_Normalize.remove_uvar_solutions env1 lax_top)
in ((

let uu____5716 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("TwoPhases")))
in (match (uu____5716) with
| true -> begin
(

let uu____5717 = (FStar_Syntax_Print.term_to_string lax_top1)
in (FStar_Util.print1 "Phase 1: checked %s\n" uu____5717))
end
| uu____5718 -> begin
()
end));
(

let uu____5719 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5719) with
| true -> begin
(check_top_level_let_rec env1 lax_top1)
end
| uu____5726 -> begin
((lax_top1), (l), (g))
end));
))
end))
end
| uu____5727 -> begin
(check_top_level_let_rec env1 top)
end));
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____5728), uu____5729) -> begin
(check_inner_let_rec env1 top)
end));
)))
and tc_synth : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env args rng -> (

let uu____5755 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.None), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5845))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.Some (a)), (rest))
end
| uu____5904 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: bad application")) rng)
end)
in (match (uu____5755) with
| (tau, atyp, rest) -> begin
(

let typ = (match (atyp) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5988 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____5988) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5994 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: need a type annotation when no expected type is present")) uu____5994))
end))
end)
in (

let uu____5997 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____5997) with
| (env', uu____6011) -> begin
(

let uu____6016 = (tc_term env' typ)
in (match (uu____6016) with
| (typ1, uu____6030, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g1);
(

let uu____6033 = (tc_tactic env' tau)
in (match (uu____6033) with
| (tau1, uu____6047, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g2);
(

let t = (match (env.FStar_TypeChecker_Env.nosynth) with
| true -> begin
(

let uu____6055 = (

let uu____6056 = (FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.magic_lid)
in (

let uu____6057 = (

let uu____6058 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____6058)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____6056 uu____6057)))
in (uu____6055 FStar_Pervasives_Native.None rng))
end
| uu____6061 -> begin
(

let t = (env.FStar_TypeChecker_Env.synth_hook env' typ1 tau1)
in ((

let uu____6064 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____6064) with
| true -> begin
(

let uu____6065 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____6065))
end
| uu____6066 -> begin
()
end));
t;
))
end)
in ((FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(

let uu____6068 = (FStar_Syntax_Syntax.mk_Tm_app t rest FStar_Pervasives_Native.None rng)
in (tc_term env uu____6068));
));
)
end));
)
end))
end)))
end)))
and tc_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___81_6072 = env
in {FStar_TypeChecker_Env.solver = uu___81_6072.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___81_6072.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___81_6072.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___81_6072.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___81_6072.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___81_6072.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___81_6072.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___81_6072.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___81_6072.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___81_6072.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___81_6072.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___81_6072.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___81_6072.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___81_6072.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___81_6072.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___81_6072.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___81_6072.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___81_6072.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___81_6072.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___81_6072.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___81_6072.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___81_6072.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___81_6072.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___81_6072.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___81_6072.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___81_6072.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___81_6072.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___81_6072.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___81_6072.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___81_6072.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___81_6072.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___81_6072.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___81_6072.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___81_6072.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___81_6072.FStar_TypeChecker_Env.dep_graph})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit)))
and tc_reified_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___82_6076 = env
in {FStar_TypeChecker_Env.solver = uu___82_6076.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___82_6076.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___82_6076.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___82_6076.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___82_6076.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___82_6076.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___82_6076.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___82_6076.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___82_6076.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___82_6076.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___82_6076.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___82_6076.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___82_6076.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___82_6076.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___82_6076.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___82_6076.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___82_6076.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___82_6076.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___82_6076.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___82_6076.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___82_6076.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___82_6076.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___82_6076.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___82_6076.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___82_6076.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___82_6076.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___82_6076.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___82_6076.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___82_6076.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___82_6076.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___82_6076.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___82_6076.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___82_6076.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___82_6076.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___82_6076.FStar_TypeChecker_Env.dep_graph})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____6092 = (tc_tactic env tactic)
in (match (uu____6092) with
| (tactic1, uu____6102, uu____6103) -> begin
FStar_Pervasives_Native.Some (tactic1)
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t0 -> (

let uu____6142 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0)
in (match (uu____6142) with
| (e2, t, implicits) -> begin
(

let tc = (

let uu____6163 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____6163) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____6168 -> begin
(

let uu____6169 = (

let uu____6170 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6170))
in FStar_Util.Inr (uu____6169))
end))
in (

let is_data_ctor = (fun uu___66_6180 -> (match (uu___66_6180) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6183)) -> begin
true
end
| uu____6190 -> begin
false
end))
in (

let uu____6193 = ((is_data_ctor dc) && (

let uu____6195 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____6195))))
in (match (uu____6193) with
| true -> begin
(

let uu____6202 = (

let uu____6207 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingDataConstructor), (uu____6207)))
in (

let uu____6208 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____6202 uu____6208)))
end
| uu____6215 -> begin
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

let uu____6225 = (

let uu____6226 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____6226))
in (failwith uu____6225))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____6260 = (

let uu____6261 = (FStar_Syntax_Subst.compress t1)
in uu____6261.FStar_Syntax_Syntax.n)
in (match (uu____6260) with
| FStar_Syntax_Syntax.Tm_arrow (uu____6264) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____6277 -> begin
(

let imp = (("uvar in term"), (env1), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___83_6315 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___83_6315.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___83_6315.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___83_6315.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env1 e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____6367 = (

let uu____6380 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____6380) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6395 = (FStar_Syntax_Util.type_u ())
in (match (uu____6395) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____6367) with
| (t, uu____6432, g0) -> begin
(

let uu____6446 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____6446) with
| (e1, uu____6466, g1) -> begin
(

let uu____6480 = (

let uu____6481 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____6481 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____6482 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e1), (uu____6480), (uu____6482))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____6484 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____6497 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____6497)))
end
| uu____6500 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____6484) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___84_6516 = x
in {FStar_Syntax_Syntax.ppname = uu___84_6516.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___84_6516.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Env.insert_bv_info env1 x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____6519 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____6519) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____6540 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____6540) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____6545 -> begin
(

let uu____6546 = (

let uu____6547 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6547))
in FStar_Util.Inr (uu____6546))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6553; FStar_Syntax_Syntax.vars = uu____6554}, uu____6555) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____6560 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____6560))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____6568 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____6568))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6576; FStar_Syntax_Syntax.vars = uu____6577}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____6586 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6586) with
| ((us', t), range) -> begin
((match ((Prims.op_disEquality (FStar_List.length us1) (FStar_List.length us'))) with
| true -> begin
(

let uu____6609 = (

let uu____6614 = (

let uu____6615 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____6616 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____6617 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____6615 uu____6616 uu____6617))))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____6614)))
in (

let uu____6618 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____6609 uu____6618)))
end
| uu____6619 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____6634 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____6638 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6638 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____6640 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6640) with
| ((us, t), range) -> begin
((

let uu____6663 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____6663) with
| true -> begin
(

let uu____6664 = (

let uu____6665 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____6665))
in (

let uu____6666 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____6667 = (FStar_Range.string_of_range range)
in (

let uu____6668 = (FStar_Range.string_of_use_range range)
in (

let uu____6669 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____6664 uu____6666 uu____6667 uu____6668 uu____6669))))))
end
| uu____6670 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____6674 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6674 us))
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

let uu____6698 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6698) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____6712 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____6712) with
| (env2, uu____6726) -> begin
(

let uu____6731 = (tc_binders env2 bs1)
in (match (uu____6731) with
| (bs2, env3, g, us) -> begin
(

let uu____6750 = (tc_comp env3 c1)
in (match (uu____6750) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___85_6769 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___85_6769.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___85_6769.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____6778 = (FStar_TypeChecker_Rel.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Rel.conj_guard g uu____6778))
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g1))));
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

let uu____6797 = (

let uu____6802 = (

let uu____6803 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6803)::[])
in (FStar_Syntax_Subst.open_term uu____6802 phi))
in (match (uu____6797) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____6813 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____6813) with
| (env2, uu____6827) -> begin
(

let uu____6832 = (

let uu____6845 = (FStar_List.hd x1)
in (tc_binder env2 uu____6845))
in (match (uu____6832) with
| (x2, env3, f1, u) -> begin
((

let uu____6873 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____6873) with
| true -> begin
(

let uu____6874 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____6875 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____6876 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____6874 uu____6875 uu____6876))))
end
| uu____6877 -> begin
()
end));
(

let uu____6878 = (FStar_Syntax_Util.type_u ())
in (match (uu____6878) with
| (t_phi, uu____6890) -> begin
(

let uu____6891 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____6891) with
| (phi2, uu____6905, f2) -> begin
(

let e1 = (

let uu___86_6910 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___86_6910.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___86_6910.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____6917 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____6917))
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____6930) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____6953 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____6953) with
| true -> begin
(

let uu____6954 = (FStar_Syntax_Print.term_to_string (

let uu___87_6957 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.pos = uu___87_6957.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___87_6957.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____6954))
end
| uu____6962 -> begin
()
end));
(

let uu____6963 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____6963) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____6976 -> begin
(

let uu____6977 = (

let uu____6978 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____6979 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____6978 uu____6979)))
in (failwith uu____6977))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Syntax_Syntax.t_unit
end
| FStar_Const.Const_bool (uu____6989) -> begin
FStar_Syntax_Util.t_bool
end
| FStar_Const.Const_int (uu____6990, FStar_Pervasives_Native.None) -> begin
FStar_Syntax_Syntax.t_int
end
| FStar_Const.Const_int (uu____7001, FStar_Pervasives_Native.Some (msize)) -> begin
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
| FStar_Const.Const_string (uu____7017) -> begin
FStar_Syntax_Syntax.t_string
end
| FStar_Const.Const_float (uu____7022) -> begin
FStar_Syntax_Syntax.t_float
end
| FStar_Const.Const_char (uu____7023) -> begin
(

let uu____7024 = (

let uu____7029 = (FStar_Syntax_DsEnv.try_lookup_lid env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid)
in (FStar_All.pipe_right uu____7029 FStar_Util.must))
in (FStar_All.pipe_right uu____7024 FStar_Pervasives_Native.fst))
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____7054) -> begin
FStar_Syntax_Syntax.t_range
end
| FStar_Const.Const_range_of -> begin
(

let uu____7055 = (

let uu____7060 = (

let uu____7061 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7061))
in ((FStar_Errors.Fatal_IllTyped), (uu____7060)))
in (FStar_Errors.raise_error uu____7055 r))
end
| FStar_Const.Const_set_range_of -> begin
(

let uu____7062 = (

let uu____7067 = (

let uu____7068 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7068))
in ((FStar_Errors.Fatal_IllTyped), (uu____7067)))
in (FStar_Errors.raise_error uu____7062 r))
end
| FStar_Const.Const_reify -> begin
(

let uu____7069 = (

let uu____7074 = (

let uu____7075 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7075))
in ((FStar_Errors.Fatal_IllTyped), (uu____7074)))
in (FStar_Errors.raise_error uu____7069 r))
end
| FStar_Const.Const_reflect (uu____7076) -> begin
(

let uu____7077 = (

let uu____7082 = (

let uu____7083 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____7083))
in ((FStar_Errors.Fatal_IllTyped), (uu____7082)))
in (FStar_Errors.raise_error uu____7077 r))
end
| uu____7084 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedConstant), ("Unsupported constant")) r)
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____7101) -> begin
(

let uu____7110 = (FStar_Syntax_Util.type_u ())
in (match (uu____7110) with
| (k, u) -> begin
(

let uu____7123 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____7123) with
| (t1, uu____7137, g) -> begin
(

let uu____7139 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____7139), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____7141) -> begin
(

let uu____7150 = (FStar_Syntax_Util.type_u ())
in (match (uu____7150) with
| (k, u) -> begin
(

let uu____7163 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____7163) with
| (t1, uu____7177, g) -> begin
(

let uu____7179 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____7179), (u), (g)))
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

let uu____7187 = (

let uu____7188 = (

let uu____7189 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____7189)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____7188))
in (uu____7187 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____7192 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____7192) with
| (tc1, uu____7206, f) -> begin
(

let uu____7208 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____7208) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____7252 = (

let uu____7253 = (FStar_Syntax_Subst.compress head3)
in uu____7253.FStar_Syntax_Syntax.n)
in (match (uu____7252) with
| FStar_Syntax_Syntax.Tm_uinst (uu____7256, us) -> begin
us
end
| uu____7262 -> begin
[]
end))
in (

let uu____7263 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____7263) with
| (uu____7284, args1) -> begin
(

let uu____7306 = (

let uu____7325 = (FStar_List.hd args1)
in (

let uu____7338 = (FStar_List.tl args1)
in ((uu____7325), (uu____7338))))
in (match (uu____7306) with
| (res, args2) -> begin
(

let uu____7403 = (

let uu____7412 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___67_7440 -> (match (uu___67_7440) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____7448 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____7448) with
| (env1, uu____7460) -> begin
(

let uu____7465 = (tc_tot_or_gtot_term env1 e)
in (match (uu____7465) with
| (e1, uu____7477, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____7412 FStar_List.unzip))
in (match (uu____7403) with
| (flags1, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___88_7516 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___88_7516.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___88_7516.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____7520 = (FStar_TypeChecker_Env.effect_repr env c2 u)
in (match (uu____7520) with
| FStar_Pervasives_Native.None -> begin
u
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____7524 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c2), (u_c), (uu____7524))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____7532) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____7533) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____7543 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____7543))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____7547 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____7547))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u2
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____7551 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____7552 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7552 FStar_Pervasives_Native.snd))
end
| uu____7561 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail1 = (fun a msg t -> (

let uu____7582 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in (FStar_Errors.raise_error uu____7582 top.FStar_Syntax_Syntax.pos)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____7676 bs2 bs_expected1 -> (match (uu____7676) with
| (env2, out, g, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.None), (g), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((match (((imp), (imp'))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7844))) -> begin
(

let uu____7849 = (

let uu____7854 = (

let uu____7855 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____7855))
in ((FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation), (uu____7854)))
in (

let uu____7856 = (FStar_Syntax_Syntax.range_of_bv hd1)
in (FStar_Errors.raise_error uu____7849 uu____7856)))
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7857)), FStar_Pervasives_Native.None) -> begin
(

let uu____7862 = (

let uu____7867 = (

let uu____7868 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____7868))
in ((FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation), (uu____7867)))
in (

let uu____7869 = (FStar_Syntax_Syntax.range_of_bv hd1)
in (FStar_Errors.raise_error uu____7862 uu____7869)))
end
| uu____7870 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____7876 = (

let uu____7881 = (

let uu____7882 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____7882.FStar_Syntax_Syntax.n)
in (match (uu____7881) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____7889 -> begin
((

let uu____7891 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____7891) with
| true -> begin
(

let uu____7892 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____7892))
end
| uu____7893 -> begin
()
end));
(

let uu____7894 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____7894) with
| (t, uu____7906, g1) -> begin
(

let g2 = (

let uu____7909 = (FStar_TypeChecker_Rel.teq_nosmt env2 t expected_t)
in (match (uu____7909) with
| true -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____7910 -> begin
(

let uu____7911 = (FStar_TypeChecker_Rel.get_subtyping_prop env2 expected_t t)
in (match (uu____7911) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7914 = (FStar_TypeChecker_Err.basic_type_error env2 FStar_Pervasives_Native.None expected_t t)
in (

let uu____7919 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____7914 uu____7919)))
end
| FStar_Pervasives_Native.Some (g2) -> begin
(

let uu____7921 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_TypeChecker_Util.label_guard uu____7921 "Type annotation on parameter incompatible with the expected type" g2))
end))
end))
in (

let g3 = (

let uu____7923 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____7923))
in ((t), (g3))))
end));
)
end))
in (match (uu____7876) with
| (t, g1) -> begin
(

let hd2 = (

let uu___89_7951 = hd1
in {FStar_Syntax_Syntax.ppname = uu___89_7951.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___89_7951.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env3 = (push_binding env2 b)
in (

let subst2 = (

let uu____7964 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____7964))
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
| uu____8112 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____8121 = (tc_binders env1 bs)
in (match (uu____8121) with
| (bs1, envbody, g, uu____8151) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody), (body1), (g))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____8195 = (

let uu____8196 = (FStar_Syntax_Subst.compress t2)
in uu____8196.FStar_Syntax_Syntax.n)
in (match (uu____8195) with
| FStar_Syntax_Syntax.Tm_uvar (uu____8219) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____8243 -> begin
(failwith "Impossible")
end);
(

let uu____8252 = (tc_binders env1 bs)
in (match (uu____8252) with
| (bs1, envbody, g, uu____8284) -> begin
(

let uu____8285 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____8285) with
| (envbody1, uu____8313) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____8324); FStar_Syntax_Syntax.pos = uu____8325; FStar_Syntax_Syntax.vars = uu____8326}, uu____8327) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____8371 -> begin
(failwith "Impossible")
end);
(

let uu____8380 = (tc_binders env1 bs)
in (match (uu____8380) with
| (bs1, envbody, g, uu____8412) -> begin
(

let uu____8413 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____8413) with
| (envbody1, uu____8441) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____8453) -> begin
(

let uu____8458 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____8458) with
| (uu____8499, bs1, bs', copt, env2, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), (bs'), (copt), (env2), (body2), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____8542 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____8542) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 body2 -> (

let rec handle_more = (fun uu____8651 c_expected2 body3 -> (match (uu____8651) with
| (env3, bs2, more, guard, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8771 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env3), (bs2), (guard), (uu____8771), (body3)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____8802 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____8802))
in (

let uu____8803 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env3), (bs2), (guard), (uu____8803), (body3))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (

let uu____8828 = ((FStar_Options.ml_ish ()) || (FStar_Syntax_Util.is_named_tot c))
in (match (uu____8828) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env3 (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____8880 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____8880) with
| (bs_expected4, c_expected4) -> begin
(

let uu____8903 = (check_binders env3 more_bs bs_expected4)
in (match (uu____8903) with
| (env4, bs', more1, guard', subst2) -> begin
(

let uu____8953 = (

let uu____8984 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env4), ((FStar_List.append bs2 bs')), (more1), (uu____8984), (subst2)))
in (handle_more uu____8953 c_expected4 body3))
end))
end))
end
| uu____9001 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env3), (bs2), (guard), (c), (body4)))
end))
end
| uu____9009 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env3), (bs2), (guard), (c), (body4)))
end)))
end)
end))
in (

let uu____9017 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____9017 c_expected1 body2))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___90_9074 = envbody
in {FStar_TypeChecker_Env.solver = uu___90_9074.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___90_9074.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___90_9074.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___90_9074.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___90_9074.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___90_9074.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___90_9074.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___90_9074.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___90_9074.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___90_9074.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___90_9074.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___90_9074.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___90_9074.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___90_9074.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___90_9074.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___90_9074.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___90_9074.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___90_9074.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___90_9074.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___90_9074.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___90_9074.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___90_9074.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___90_9074.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___90_9074.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___90_9074.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___90_9074.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___90_9074.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___90_9074.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___90_9074.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___90_9074.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___90_9074.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___90_9074.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___90_9074.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___90_9074.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___90_9074.FStar_TypeChecker_Env.dep_graph})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____9122 uu____9123 -> (match (((uu____9122), (uu____9123))) with
| ((env2, letrec_binders), (l, t3, u_names)) -> begin
(

let uu____9185 = (

let uu____9192 = (

let uu____9193 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____9193 FStar_Pervasives_Native.fst))
in (tc_term uu____9192 t3))
in (match (uu____9185) with
| (t4, uu____9215, uu____9216) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l ((u_names), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____9226 = (FStar_Syntax_Syntax.mk_binder (

let uu___91_9229 = x
in {FStar_Syntax_Syntax.ppname = uu___91_9229.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___91_9229.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____9226)::letrec_binders)
end
| uu____9230 -> begin
letrec_binders
end)
in ((env3), (lb))))
end))
end)) ((envbody1), ([])))))))
in (

let uu____9235 = (check_actuals_against_formals env1 bs bs_expected1 body1)
in (match (uu____9235) with
| (envbody, bs1, g, c, body2) -> begin
(

let uu____9289 = (mk_letrec_env envbody bs1 c)
in (match (uu____9289) with
| (envbody1, letrecs) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in ((FStar_Pervasives_Native.Some (t2)), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (envbody2), (body2), (g)))
end))
end))))
end))
end
| uu____9335 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____9356 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____9356))
end
| uu____9357 -> begin
(

let uu____9358 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____9358) with
| (uu____9397, bs1, uu____9399, c_opt, envbody, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (c_opt), (envbody), (body2), (g))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____9419 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9419) with
| (env1, topt) -> begin
((

let uu____9439 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____9439) with
| true -> begin
(

let uu____9440 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____9440 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____9442 -> begin
"false"
end)))
end
| uu____9443 -> begin
()
end));
(

let uu____9444 = (expected_function_typ1 env1 topt body)
in (match (uu____9444) with
| (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1, g) -> begin
(

let uu____9484 = (

let should_check_expected_effect = (

let uu____9492 = (

let uu____9499 = (

let uu____9500 = (FStar_Syntax_Subst.compress body1)
in uu____9500.FStar_Syntax_Syntax.n)
in ((c_opt), (uu____9499)))
in (match (uu____9492) with
| (FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Tm_ascribed (uu____9505, (FStar_Util.Inr (expected_c), uu____9507), uu____9508)) -> begin
false
end
| uu____9557 -> begin
true
end))
in (

let uu____9564 = (tc_term (

let uu___92_9573 = envbody
in {FStar_TypeChecker_Env.solver = uu___92_9573.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___92_9573.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___92_9573.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___92_9573.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___92_9573.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___92_9573.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___92_9573.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___92_9573.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___92_9573.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___92_9573.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___92_9573.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___92_9573.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___92_9573.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___92_9573.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___92_9573.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___92_9573.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___92_9573.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___92_9573.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___92_9573.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___92_9573.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___92_9573.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___92_9573.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___92_9573.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___92_9573.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___92_9573.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___92_9573.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___92_9573.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___92_9573.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___92_9573.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___92_9573.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___92_9573.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___92_9573.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___92_9573.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___92_9573.FStar_TypeChecker_Env.dep_graph}) body1)
in (match (uu____9564) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (match (should_check_expected_effect) with
| true -> begin
(

let uu____9590 = (

let uu____9597 = (

let uu____9602 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____9602)))
in (check_expected_effect (

let uu___93_9605 = envbody
in {FStar_TypeChecker_Env.solver = uu___93_9605.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___93_9605.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___93_9605.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___93_9605.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___93_9605.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___93_9605.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___93_9605.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___93_9605.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___93_9605.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___93_9605.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___93_9605.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___93_9605.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___93_9605.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___93_9605.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___93_9605.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___93_9605.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___93_9605.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___93_9605.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___93_9605.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___93_9605.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___93_9605.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___93_9605.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___93_9605.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___93_9605.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___93_9605.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___93_9605.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___93_9605.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___93_9605.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___93_9605.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___93_9605.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___93_9605.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___93_9605.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___93_9605.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___93_9605.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___93_9605.FStar_TypeChecker_Env.dep_graph}) c_opt uu____9597))
in (match (uu____9590) with
| (body3, cbody1, guard) -> begin
(

let uu____9615 = (FStar_TypeChecker_Rel.conj_guard guard_body1 guard)
in ((body3), (cbody1), (uu____9615)))
end))
end
| uu____9616 -> begin
(

let uu____9617 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____9617), (guard_body1)))
end))
end)))
in (match (uu____9484) with
| (body2, cbody, guard) -> begin
(

let guard1 = (

let uu____9628 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____9630 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____9630))))
in (match (uu____9628) with
| true -> begin
(

let uu____9631 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____9631))
end
| uu____9632 -> begin
(

let guard1 = (

let uu____9634 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard env1 (FStar_List.append bs1 letrec_binders) uu____9634))
in guard1)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody)
in (

let e = (FStar_Syntax_Util.abs bs1 body2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody c_opt)))))
in (

let uu____9643 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____9664) -> begin
((e), (t1), (guard1))
end
| uu____9677 -> begin
(

let uu____9678 = (FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
in (match (uu____9678) with
| (e1, guard') -> begin
(

let uu____9691 = (FStar_TypeChecker_Rel.conj_guard guard1 guard')
in ((e1), (t1), (uu____9691)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard1))
end)
in (match (uu____9643) with
| (e1, tfun, guard2) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Total tfun)
in (

let uu____9704 = (

let uu____9709 = (FStar_Syntax_Util.lcomp_of_comp c)
in (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 uu____9709 guard2))
in (match (uu____9704) with
| (c1, g1) -> begin
((e1), (c1), (g1))
end)))
end)))))
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

let uu____9754 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____9754) with
| true -> begin
(

let uu____9755 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____9756 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____9755 uu____9756)))
end
| uu____9757 -> begin
()
end));
(

let monadic_application = (fun uu____9813 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____9813) with
| (head2, chead1, ghead1, cres) -> begin
(

let rt = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres1 = (

let uu___94_9872 = cres
in {FStar_Syntax_Syntax.eff_name = uu___94_9872.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___94_9872.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___94_9872.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____9873 = (match (bs) with
| [] -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in ((cres1), (g)))
end
| uu____9887 -> begin
(

let g = (

let uu____9895 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____9895 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (

let uu____9896 = (

let uu____9897 = (

let uu____9900 = (

let uu____9901 = (FStar_Syntax_Syntax.lcomp_comp cres1)
in (FStar_Syntax_Util.arrow bs uu____9901))
in (FStar_Syntax_Syntax.mk_Total uu____9900))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____9897))
in ((uu____9896), (g))))
end)
in (match (uu____9873) with
| (cres2, guard1) -> begin
((

let uu____9915 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____9915) with
| true -> begin
(

let uu____9916 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____9916))
end
| uu____9917 -> begin
()
end));
(

let cres3 = (

let head_is_pure_and_some_arg_is_effectful = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1) && (FStar_Util.for_some (fun uu____9932 -> (match (uu____9932) with
| (uu____9941, uu____9942, lc) -> begin
((

let uu____9950 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____9950))) || (FStar_TypeChecker_Util.should_not_inline_lc lc))
end)) arg_comps_rev))
in (

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (

let uu____9960 = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2) && head_is_pure_and_some_arg_is_effectful)
in (match (uu____9960) with
| true -> begin
((

let uu____9962 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9962) with
| true -> begin
(

let uu____9963 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: Return inserted in monadic application: %s\n" uu____9963))
end
| uu____9964 -> begin
()
end));
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2);
)
end
| uu____9965 -> begin
((

let uu____9967 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9967) with
| true -> begin
(

let uu____9968 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: No return inserted in monadic application: %s\n" uu____9968))
end
| uu____9969 -> begin
()
end));
cres2;
)
end))))
in (

let comp = (FStar_List.fold_left (fun out_c uu____9992 -> (match (uu____9992) with
| ((e, q), x, c) -> begin
((

let uu____10018 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10018) with
| true -> begin
(

let uu____10019 = (match (x) with
| FStar_Pervasives_Native.None -> begin
"_"
end
| FStar_Pervasives_Native.Some (x1) -> begin
(FStar_Syntax_Print.bv_to_string x1)
end)
in (

let uu____10021 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print2 "(b) Monadic app: Binding argument %s : %s\n" uu____10019 uu____10021)))
end
| uu____10022 -> begin
()
end));
(

let uu____10023 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____10023) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____10026 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end));
)
end)) cres3 arg_comps_rev)
in (

let comp1 = ((

let uu____10031 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10031) with
| true -> begin
(

let uu____10032 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print1 "(c) Monadic app: Binding head %s " uu____10032))
end
| uu____10033 -> begin
()
end));
(

let uu____10034 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1)
in (match (uu____10034) with
| true -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (head2)) chead1 ((FStar_Pervasives_Native.None), (comp)))
end
| uu____10037 -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
end));
)
in (

let comp2 = (FStar_TypeChecker_Util.subst_lcomp subst1 comp1)
in (

let shortcuts_evaluation_order = (

let uu____10042 = (

let uu____10043 = (FStar_Syntax_Subst.compress head2)
in uu____10043.FStar_Syntax_Syntax.n)
in (match (uu____10042) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____10047 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____10068 -> (match (uu____10068) with
| (arg, uu____10082, uu____10083) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ))))
end
| uu____10092 -> begin
(

let uu____10093 = (

let map_fun = (fun uu____10155 -> (match (uu____10155) with
| ((e, q), uu____10190, c) -> begin
(

let uu____10200 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____10200) with
| true -> begin
((FStar_Pervasives_Native.None), (((e), (q))))
end
| uu____10247 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____10250 = (

let uu____10255 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____10255), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____10250)))))
end))
end))
in (

let uu____10284 = (

let uu____10309 = (

let uu____10332 = (

let uu____10347 = (

let uu____10356 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____10356), (FStar_Pervasives_Native.None), (chead1)))
in (uu____10347)::arg_comps_rev)
in (FStar_List.map map_fun uu____10332))
in (FStar_All.pipe_left FStar_List.split uu____10309))
in (match (uu____10284) with
| (lifted_args, reverse_args) -> begin
(

let uu____10529 = (

let uu____10530 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____10530))
in (

let uu____10539 = (

let uu____10546 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____10546))
in ((lifted_args), (uu____10529), (uu____10539))))
end)))
in (match (uu____10093) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___68_10649 -> (match (uu___68_10649) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1 [] e1.FStar_Syntax_Syntax.pos)
in (

let letbinding = (

let uu____10706 = (

let uu____10709 = (

let uu____10710 = (

let uu____10723 = (

let uu____10724 = (

let uu____10725 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____10725)::[])
in (FStar_Syntax_Subst.close uu____10724 e))
in ((((false), ((lb)::[]))), (uu____10723)))
in FStar_Syntax_Syntax.Tm_let (uu____10710))
in (FStar_Syntax_Syntax.mk uu____10709))
in (uu____10706 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp2.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____10755 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp2 guard1)
in (match (uu____10755) with
| (comp3, g) -> begin
((

let uu____10771 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10771) with
| true -> begin
(

let uu____10772 = (FStar_Syntax_Print.term_to_string app)
in (

let uu____10773 = (FStar_Syntax_Print.lcomp_to_string comp3)
in (FStar_Util.print2 "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n" uu____10772 uu____10773)))
end
| uu____10774 -> begin
()
end));
((app), (comp3), (g));
)
end))))))));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____10849 bs args1 -> (match (uu____10849) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10992))))::rest, ((uu____10994, FStar_Pervasives_Native.None))::uu____10995) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let t1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (

let uu____11046 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____11046) with
| (varg, uu____11066, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____11088 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____11088)))
in (

let uu____11089 = (

let uu____11124 = (

let uu____11139 = (

let uu____11152 = (

let uu____11153 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____11153 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____11152)))
in (uu____11139)::outargs)
in (

let uu____11172 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst2), (uu____11124), ((arg)::arg_rets), (uu____11172), (fvs))))
in (tc_args head_info uu____11089 rest args1))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11264)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11265))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____11278 -> begin
(

let uu____11287 = (

let uu____11292 = (

let uu____11293 = (FStar_Syntax_Print.aqual_to_string aqual)
in (

let uu____11294 = (FStar_Syntax_Print.aqual_to_string aq)
in (

let uu____11295 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____11296 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format4 "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s" uu____11293 uu____11294 uu____11295 uu____11296)))))
in ((FStar_Errors.Fatal_InconsistentImplicitQualifier), (uu____11292)))
in (FStar_Errors.raise_error uu____11287 e.FStar_Syntax_Syntax.pos))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___95_11299 = x
in {FStar_Syntax_Syntax.ppname = uu___95_11299.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___95_11299.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____11301 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____11301) with
| true -> begin
(

let uu____11302 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____11302))
end
| uu____11303 -> begin
()
end));
(

let targ1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___96_11307 = env1
in {FStar_TypeChecker_Env.solver = uu___96_11307.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_11307.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_11307.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_11307.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___96_11307.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_11307.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_11307.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_11307.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_11307.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_11307.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_11307.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_11307.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___96_11307.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___96_11307.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___96_11307.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___96_11307.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_11307.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___96_11307.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___96_11307.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___96_11307.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___96_11307.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___96_11307.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___96_11307.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_11307.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___96_11307.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_11307.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___96_11307.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___96_11307.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___96_11307.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___96_11307.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___96_11307.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___96_11307.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___96_11307.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___96_11307.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___96_11307.FStar_TypeChecker_Env.dep_graph})
in ((

let uu____11309 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____11309) with
| true -> begin
(

let uu____11310 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____11311 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11312 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____11310 uu____11311 uu____11312))))
end
| uu____11313 -> begin
()
end));
(

let uu____11314 = (tc_term env2 e)
in (match (uu____11314) with
| (e1, c, g_e) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____11349 = (

let uu____11352 = (

let uu____11359 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____11359))
in (FStar_Pervasives_Native.fst uu____11352))
in ((uu____11349), (aq)))
in (

let uu____11366 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____11366) with
| true -> begin
(

let subst2 = (

let uu____11374 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____11374 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____11439 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
))));
)));
)
end
| (uu____11500, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____11532) -> begin
(

let uu____11575 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____11575) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 tres -> (

let tres1 = (

let uu____11609 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____11609 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____11634 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____11634) with
| (bs2, cres'1) -> begin
(

let head_info1 = (

let uu____11656 = (FStar_Syntax_Util.lcomp_of_comp cres'1)
in ((head2), (chead1), (ghead1), (uu____11656)))
in ((

let uu____11658 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____11658) with
| true -> begin
(FStar_Errors.log_issue tres1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_RedundantExplicitCurrying), ("Potentially redundant explicit currying of a function type")))
end
| uu____11659 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____11700 when (not (norm1)) -> begin
(

let rec norm_tres = (fun tres2 -> (

let tres3 = (FStar_TypeChecker_Normalize.unfold_whnf env tres2)
in (

let uu____11706 = (

let uu____11707 = (FStar_Syntax_Subst.compress tres3)
in uu____11707.FStar_Syntax_Syntax.n)
in (match (uu____11706) with
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____11710; FStar_Syntax_Syntax.index = uu____11711; FStar_Syntax_Syntax.sort = tres4}, uu____11713) -> begin
(norm_tres tres4)
end
| uu____11720 -> begin
tres3
end))))
in (

let uu____11721 = (norm_tres tres1)
in (aux true uu____11721)))
end
| uu____11722 -> begin
(

let uu____11723 = (

let uu____11728 = (

let uu____11729 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____11730 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" uu____11729 uu____11730)))
in ((FStar_Errors.Fatal_ToManyArgumentToFunction), (uu____11728)))
in (

let uu____11737 = (FStar_Syntax_Syntax.argpos arg)
in (FStar_Errors.raise_error uu____11723 uu____11737)))
end)))
in (aux false chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf -> (

let uu____11756 = (

let uu____11757 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____11757.FStar_Syntax_Syntax.n)
in (match (uu____11756) with
| FStar_Syntax_Syntax.Tm_uvar (uu____11768) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____11869 = (tc_term env1 e)
in (match (uu____11869) with
| (e1, c, g_e) -> begin
(

let uu____11891 = (tc_args1 env1 tl1)
in (match (uu____11891) with
| (args2, comps, g_rest) -> begin
(

let uu____11931 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____11931)))
end))
end))
end))
in (

let uu____11952 = (tc_args1 env args)
in (match (uu____11952) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____11989 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____12027 -> (match (uu____12027) with
| (uu____12040, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____11989))
in (

let ml_or_tot = (fun t r1 -> (

let uu____12057 = (FStar_Options.ml_ish ())
in (match (uu____12057) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____12058 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____12060 = (

let uu____12063 = (

let uu____12064 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12064 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____12063))
in (ml_or_tot uu____12060 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____12077 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____12077) with
| true -> begin
(

let uu____12078 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____12079 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____12080 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____12078 uu____12079 uu____12080))))
end
| uu____12081 -> begin
()
end));
(

let uu____12083 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____12083));
(

let comp = (

let uu____12085 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____12096 out -> (match (uu____12096) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____12085))
in (

let uu____12110 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let uu____12113 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____12110), (comp), (uu____12113)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12116); FStar_Syntax_Syntax.pos = uu____12117; FStar_Syntax_Syntax.vars = uu____12118}, uu____12119) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____12240 = (tc_term env1 e)
in (match (uu____12240) with
| (e1, c, g_e) -> begin
(

let uu____12262 = (tc_args1 env1 tl1)
in (match (uu____12262) with
| (args2, comps, g_rest) -> begin
(

let uu____12302 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____12302)))
end))
end))
end))
in (

let uu____12323 = (tc_args1 env args)
in (match (uu____12323) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____12360 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____12398 -> (match (uu____12398) with
| (uu____12411, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____12360))
in (

let ml_or_tot = (fun t r1 -> (

let uu____12428 = (FStar_Options.ml_ish ())
in (match (uu____12428) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____12429 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____12431 = (

let uu____12434 = (

let uu____12435 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____12435 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____12434))
in (ml_or_tot uu____12431 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____12448 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____12448) with
| true -> begin
(

let uu____12449 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____12450 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____12451 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____12449 uu____12450 uu____12451))))
end
| uu____12452 -> begin
()
end));
(

let uu____12454 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____12454));
(

let comp = (

let uu____12456 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____12467 out -> (match (uu____12467) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____12456))
in (

let uu____12481 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let uu____12484 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____12481), (comp), (uu____12484)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____12505 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____12505) with
| (bs1, c1) -> begin
(

let head_info = (

let uu____12529 = (FStar_Syntax_Util.lcomp_of_comp c1)
in ((head1), (chead), (ghead), (uu____12529)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs1 args))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____12571) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____12577, uu____12578) -> begin
(check_function_app t)
end
| uu____12619 -> begin
(

let uu____12620 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in (FStar_Errors.raise_error uu____12620 head1.FStar_Syntax_Syntax.pos))
end)))
in (check_function_app thead))));
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

let uu____12694 = (FStar_List.fold_left2 (fun uu____12737 uu____12738 uu____12739 -> (match (((uu____12737), (uu____12738), (uu____12739))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((Prims.op_disEquality aq aq')) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InconsistentImplicitQualifier), ("Inconsistent implicit qualifiers")) e.FStar_Syntax_Syntax.pos)
end
| uu____12806 -> begin
()
end);
(

let uu____12807 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____12807) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____12825 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____12825 g))
in (

let ghost1 = (ghost || ((

let uu____12829 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____12829))) && (

let uu____12831 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____12831)))))
in (

let uu____12832 = (

let uu____12841 = (

let uu____12850 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____12850)::[])
in (FStar_List.append seen uu____12841))
in (

let uu____12857 = (FStar_TypeChecker_Rel.conj_guard guard g1)
in ((uu____12832), (uu____12857), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____12694) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____12893 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____12893 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____12894 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____12895 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____12895) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____12912 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp) * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____12954 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____12954) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____12998 = branch1
in (match (uu____12998) with
| (cpat, uu____13038, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let tc_annot = (fun env1 t -> (

let uu____13105 = (FStar_Syntax_Util.type_u ())
in (match (uu____13105) with
| (tu, u) -> begin
(

let uu____13116 = (tc_check_tot_or_gtot_term env1 t tu)
in (match (uu____13116) with
| (t1, uu____13128, g) -> begin
((t1), (g))
end))
end)))
in (

let uu____13130 = (FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 tc_annot)
in (match (uu____13130) with
| (pat_bvs1, exp, guard_pat_annots, p) -> begin
((

let uu____13164 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13164) with
| true -> begin
(

let uu____13165 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____13166 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____13165 uu____13166)))
end
| uu____13167 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs1)
in (

let uu____13169 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____13169) with
| (env1, uu____13191) -> begin
(

let env11 = (

let uu___97_13197 = env1
in {FStar_TypeChecker_Env.solver = uu___97_13197.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___97_13197.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___97_13197.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___97_13197.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___97_13197.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___97_13197.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___97_13197.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___97_13197.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___97_13197.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___97_13197.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___97_13197.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___97_13197.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___97_13197.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___97_13197.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___97_13197.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___97_13197.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___97_13197.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___97_13197.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___97_13197.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___97_13197.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___97_13197.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___97_13197.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___97_13197.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___97_13197.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___97_13197.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___97_13197.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___97_13197.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___97_13197.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___97_13197.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___97_13197.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___97_13197.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___97_13197.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___97_13197.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___97_13197.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___97_13197.FStar_TypeChecker_Env.dep_graph})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in ((

let uu____13200 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13200) with
| true -> begin
(

let uu____13201 = (FStar_Syntax_Print.term_to_string exp)
in (

let uu____13202 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____13201 uu____13202)))
end
| uu____13203 -> begin
()
end));
(

let env12 = (FStar_TypeChecker_Env.set_expected_typ env11 expected_pat_t)
in (

let uu____13205 = (tc_tot_or_gtot_term env12 exp)
in (match (uu____13205) with
| (exp1, lc, g) -> begin
(

let g1 = (

let uu___98_13230 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___98_13230.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___98_13230.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___98_13230.FStar_TypeChecker_Env.implicits})
in (

let uu____13231 = (

let uu____13232 = (FStar_TypeChecker_Rel.teq_nosmt env12 lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (match (uu____13232) with
| true -> begin
(

let env13 = (FStar_TypeChecker_Env.set_range env12 exp1.FStar_Syntax_Syntax.pos)
in (

let uu____13234 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env13 g1)
in (FStar_All.pipe_right uu____13234 FStar_TypeChecker_Rel.resolve_implicits)))
end
| uu____13235 -> begin
(

let uu____13236 = (

let uu____13241 = (

let uu____13242 = (FStar_Syntax_Print.term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____13243 = (FStar_Syntax_Print.term_to_string expected_pat_t)
in (FStar_Util.format2 "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)" uu____13242 uu____13243)))
in ((FStar_Errors.Fatal_MismatchedPatternType), (uu____13241)))
in (FStar_Errors.raise_error uu____13236 exp1.FStar_Syntax_Syntax.pos))
end))
in (

let norm_exp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env12 exp1)
in (

let uvs_to_string = (fun uvs -> (

let uu____13261 = (

let uu____13264 = (FStar_Util.set_elements uvs)
in (FStar_All.pipe_right uu____13264 (FStar_List.map (fun uu____13290 -> (match (uu____13290) with
| (u, uu____13296) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right uu____13261 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars norm_exp)
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____13314 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Free")))
in (match (uu____13314) with
| true -> begin
((

let uu____13316 = (FStar_Syntax_Print.term_to_string norm_exp)
in (

let uu____13317 = (uvs_to_string uvs1)
in (FStar_Util.print2 ">> free_1(%s) = %s\n" uu____13316 uu____13317)));
(

let uu____13318 = (FStar_Syntax_Print.term_to_string expected_pat_t)
in (

let uu____13319 = (uvs_to_string uvs2)
in (FStar_Util.print2 ">> free_2(%s) = %s\n" uu____13318 uu____13319)));
)
end
| uu____13320 -> begin
()
end));
(

let uu____13322 = (

let uu____13323 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____13323))
in (match (uu____13322) with
| true -> begin
(

let unresolved = (FStar_Util.set_difference uvs1 uvs2)
in (

let uu____13339 = (

let uu____13344 = (

let uu____13345 = (FStar_TypeChecker_Normalize.term_to_string env norm_exp)
in (

let uu____13346 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____13347 = (uvs_to_string unresolved)
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____13345 uu____13346 uu____13347))))
in ((FStar_Errors.Fatal_UnresolvedPatternVar), (uu____13344)))
in (FStar_Errors.raise_error uu____13339 p.FStar_Syntax_Syntax.p)))
end
| uu____13348 -> begin
()
end));
(

let uu____13350 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____13350) with
| true -> begin
(

let uu____13351 = (FStar_TypeChecker_Normalize.term_to_string env exp1)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____13351))
end
| uu____13352 -> begin
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

let uu____13360 = (

let uu____13367 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____13367 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____13360) with
| (scrutinee_env, uu____13399) -> begin
(

let uu____13404 = (tc_pat true pat_t pattern)
in (match (uu____13404) with
| (pattern1, pat_bvs1, pat_env, pat_exp, guard_pat_annots, norm_pat_exp) -> begin
(

let uu____13453 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____13475 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____13475) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_WhenClauseNotSupported), ("When clauses are not yet supported in --verify mode; they will be some day")) e.FStar_Syntax_Syntax.pos)
end
| uu____13488 -> begin
(

let uu____13489 = (

let uu____13496 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_Syntax_Util.t_bool)
in (tc_term uu____13496 e))
in (match (uu____13489) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____13453) with
| (when_clause1, g_when) -> begin
(

let uu____13538 = (tc_term pat_env branch_exp)
in (match (uu____13538) with
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

let uu____13579 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____13579))
end)
in (

let uu____13582 = (

let eqs = (

let uu____13600 = (

let uu____13601 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____13601)))
in (match (uu____13600) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13604 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____13608) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____13625) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____13626) -> begin
FStar_Pervasives_Native.None
end
| uu____13627 -> begin
(

let uu____13628 = (

let uu____13629 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____13629 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____13628))
end))
end))
in (

let uu____13630 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch1)
in (match (uu____13630) with
| (c1, g_branch2) -> begin
(

let uu____13653 = (match (((eqs), (when_condition))) with
| uu____13666 when (

let uu____13675 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____13675))) -> begin
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

let uu____13687 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____13688 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____13687), (uu____13688))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____13697 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____13697))
in (

let uu____13698 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____13699 = (

let uu____13700 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____13700 g_when))
in ((uu____13698), (uu____13699))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____13708 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____13708), (g_when)))))
end)
in (match (uu____13653) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let maybe_return_c_weak = (fun should_return -> (

let c_weak1 = (

let uu____13733 = (should_return && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c_weak))
in (match (uu____13733) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env branch_exp1 c_weak)
end
| uu____13734 -> begin
c_weak
end))
in (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak1)))
in (

let uu____13735 = (FStar_TypeChecker_Rel.close_guard env binders g_when_weak)
in ((c_weak.FStar_Syntax_Syntax.eff_name), (c_weak.FStar_Syntax_Syntax.cflags), (maybe_return_c_weak), (uu____13735), (g_branch2)))))
end))
end)))
in (match (uu____13582) with
| (effect_label, cflags, maybe_return_c, g_when1, g_branch2) -> begin
(

let branch_guard = (

let uu____13778 = (

let uu____13779 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____13779)))
in (match (uu____13778) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____13780 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____13809 = (

let uu____13810 = (

let uu____13811 = (

let uu____13814 = (

let uu____13821 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____13821))
in (FStar_Pervasives_Native.snd uu____13814))
in (FStar_List.length uu____13811))
in (uu____13810 > (Prims.parse_int "1")))
in (match (uu____13809) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____13827 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____13827) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____13848 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____13863 = (

let uu____13864 = (

let uu____13865 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____13865)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____13864))
in (uu____13863 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____13868 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____13868)::[])))
end)))
end
| uu____13869 -> begin
[]
end)))
in (

let fail1 = (fun uu____13873 -> (

let uu____13874 = (

let uu____13875 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____13876 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____13877 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____13875 uu____13876 uu____13877))))
in (failwith uu____13874)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____13888) -> begin
(head_constructor t1)
end
| uu____13893 -> begin
(fail1 ())
end))
in (

let pat_exp2 = (

let uu____13895 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____13895 FStar_Syntax_Util.unmeta))
in (match (pat_exp2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____13898) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____13915); FStar_Syntax_Syntax.pos = uu____13916; FStar_Syntax_Syntax.vars = uu____13917}, uu____13918) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_name (uu____13955) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (c1) -> begin
(

let uu____13957 = (

let uu____13958 = (tc_constant env pat_exp2.FStar_Syntax_Syntax.pos c1)
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____13958 scrutinee_tm1 pat_exp2))
in (uu____13957)::[])
end
| FStar_Syntax_Syntax.Tm_uinst (uu____13959) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____13967 = (

let uu____13968 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____13968)))
in (match (uu____13967) with
| true -> begin
[]
end
| uu____13971 -> begin
(

let uu____13972 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____13972))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____13975) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____13977 = (

let uu____13978 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____13978)))
in (match (uu____13977) with
| true -> begin
[]
end
| uu____13981 -> begin
(

let uu____13982 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____13982))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let f = (head_constructor head1)
in (

let uu____14008 = (

let uu____14009 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____14009)))
in (match (uu____14008) with
| true -> begin
[]
end
| uu____14012 -> begin
(

let sub_term_guards = (

let uu____14016 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____14048 -> (match (uu____14048) with
| (ei, uu____14058) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____14064 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____14064) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____14085 -> begin
(

let sub_term = (

let uu____14099 = (

let uu____14100 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____14101 = (

let uu____14102 = (FStar_Syntax_Syntax.as_arg scrutinee_tm1)
in (uu____14102)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____14100 uu____14101)))
in (uu____14099 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____14016 FStar_List.flatten))
in (

let uu____14111 = (discriminate scrutinee_tm1 f)
in (FStar_List.append uu____14111 sub_term_guards)))
end)))
end
| uu____14114 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pat -> (

let uu____14126 = (

let uu____14127 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____14127)))
in (match (uu____14126) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____14128 -> begin
(

let t = (

let uu____14130 = (build_branch_guard scrutinee_tm1 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____14130))
in (

let uu____14135 = (FStar_Syntax_Util.type_u ())
in (match (uu____14135) with
| (k, uu____14141) -> begin
(

let uu____14142 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____14142) with
| (t1, uu____14150, uu____14151) -> begin
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

let uu____14157 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____14157) with
| true -> begin
(

let uu____14158 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____14158))
end
| uu____14159 -> begin
()
end));
(

let uu____14160 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in ((uu____14160), (branch_guard), (effect_label), (cflags), (maybe_return_c), (guard)));
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

let uu____14190 = (check_let_bound_def true env1 lb)
in (match (uu____14190) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____14212 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____14229 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____14229), (univ_vars1), (c1)))
end
| uu____14230 -> begin
(

let g11 = (

let uu____14232 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____14232 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____14242 = (

let uu____14255 = (

let uu____14270 = (

let uu____14279 = (

let uu____14290 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____14290)))
in (uu____14279)::[])
in (FStar_TypeChecker_Util.generalize env1 false uu____14270))
in (FStar_List.hd uu____14255))
in (match (uu____14242) with
| (uu____14335, univs1, e11, c11, gvs) -> begin
(

let g12 = (FStar_All.pipe_left (FStar_TypeChecker_Rel.map_guard g11) (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env1))
in (

let g13 = (FStar_TypeChecker_Rel.abstract_guard_n gvs g12)
in (

let uu____14348 = (FStar_Syntax_Util.lcomp_of_comp c11)
in ((g13), (e11), (univs1), (uu____14348)))))
end)))
end)
in (match (uu____14212) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____14359 = (

let uu____14366 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____14366) with
| true -> begin
(

let uu____14373 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____14373) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____14394 -> begin
((

let uu____14396 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____14396 FStar_TypeChecker_Err.top_level_effect));
(

let uu____14397 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____14397), (c12)));
)
end)
end))
end
| uu____14404 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____14407 = (FStar_Syntax_Syntax.lcomp_comp c11)
in (FStar_All.pipe_right uu____14407 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env1)))
in (

let e21 = (

let uu____14411 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____14411) with
| true -> begin
e2
end
| uu____14414 -> begin
((

let uu____14416 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____14416 FStar_TypeChecker_Err.top_level_effect));
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos);
)
end))
in ((e21), (c))));
)
end))
in (match (uu____14359) with
| (e21, c12) -> begin
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit)
in (

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e11 lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
in (

let uu____14437 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____14450 = (FStar_Syntax_Util.lcomp_of_comp cres)
in ((uu____14437), (uu____14450), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| uu____14453 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___99_14484 = env1
in {FStar_TypeChecker_Env.solver = uu___99_14484.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___99_14484.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___99_14484.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___99_14484.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___99_14484.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___99_14484.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___99_14484.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___99_14484.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___99_14484.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___99_14484.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___99_14484.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___99_14484.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___99_14484.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___99_14484.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___99_14484.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___99_14484.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___99_14484.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___99_14484.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___99_14484.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___99_14484.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___99_14484.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___99_14484.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___99_14484.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___99_14484.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___99_14484.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___99_14484.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___99_14484.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___99_14484.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___99_14484.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___99_14484.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___99_14484.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___99_14484.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___99_14484.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___99_14484.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___99_14484.FStar_TypeChecker_Env.dep_graph})
in (

let uu____14485 = (

let uu____14496 = (

let uu____14497 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____14497 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____14496 lb))
in (match (uu____14485) with
| (e1, uu____14519, c1, g1, annotated) -> begin
((

let uu____14524 = ((FStar_Util.for_some (FStar_Syntax_Util.is_fvar FStar_Parser_Const.inline_let_attr) lb.FStar_Syntax_Syntax.lbattrs) && (

let uu____14526 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c1)
in (not (uu____14526))))
in (match (uu____14524) with
| true -> begin
(

let uu____14527 = (

let uu____14532 = (

let uu____14533 = (FStar_Syntax_Print.term_to_string e1)
in (

let uu____14534 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.format2 "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\"" uu____14533 uu____14534)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____14532)))
in (FStar_Errors.raise_error uu____14527 e1.FStar_Syntax_Syntax.pos))
end
| uu____14535 -> begin
()
end));
(

let x = (

let uu___100_14537 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___100_14537.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___100_14537.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____14538 = (

let uu____14543 = (

let uu____14544 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____14544)::[])
in (FStar_Syntax_Subst.open_term uu____14543 e2))
in (match (uu____14538) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let env_x = (FStar_TypeChecker_Env.push_bv env2 x1)
in (

let uu____14564 = (tc_term env_x e21)
in (match (uu____14564) with
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

let uu____14589 = (

let uu____14592 = (

let uu____14593 = (

let uu____14606 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____14606)))
in FStar_Syntax_Syntax.Tm_let (uu____14593))
in (FStar_Syntax_Syntax.mk uu____14592))
in (uu____14589 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____14620 = (

let uu____14621 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____14622 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____14621 c1.FStar_Syntax_Syntax.res_typ uu____14622 e11)))
in (FStar_All.pipe_left (fun _0_42 -> FStar_TypeChecker_Common.NonTrivial (_0_42)) uu____14620))
in (

let g21 = (

let uu____14624 = (

let uu____14625 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____14625 g2))
in (FStar_TypeChecker_Rel.close_guard env2 xb uu____14624))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g21)
in (

let uu____14627 = (

let uu____14628 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____14628))
in (match (uu____14627) with
| true -> begin
(

let tt = (

let uu____14638 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____14638 FStar_Option.get))
in ((

let uu____14644 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____14644) with
| true -> begin
(

let uu____14645 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____14646 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____14645 uu____14646)))
end
| uu____14647 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____14648 -> begin
(

let t = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____14651 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____14651) with
| true -> begin
(

let uu____14652 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____14653 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____14652 uu____14653)))
end
| uu____14654 -> begin
()
end));
((e4), ((

let uu___101_14656 = cres
in {FStar_Syntax_Syntax.eff_name = uu___101_14656.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___101_14656.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___101_14656.FStar_Syntax_Syntax.comp_thunk})), (guard));
))
end)))))))))))
end)))))
end)));
)
end)))
end
| uu____14657 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____14689 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____14689) with
| (lbs1, e21) -> begin
(

let uu____14708 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____14708) with
| (env0, topt) -> begin
(

let uu____14727 = (build_let_rec_env true env0 lbs1)
in (match (uu____14727) with
| (lbs2, rec_env) -> begin
(

let uu____14746 = (check_let_recs rec_env lbs2)
in (match (uu____14746) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____14766 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g_lbs)
in (FStar_All.pipe_right uu____14766 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (

let uu____14772 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____14772 (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((Prims.op_Equality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
lb
end
| uu____14804 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)))))
end
| uu____14805 -> begin
(

let ecs = (

let uu____14821 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____14861 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____14861))))))
in (FStar_TypeChecker_Util.generalize env1 true uu____14821))
in (FStar_List.map2 (fun uu____14895 lb -> (match (uu____14895) with
| (x, uvs, e, c, gvs) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)) ecs lbs3))
end)
in (

let cres = (

let uu____14943 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____14943))
in (

let uu____14948 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____14948) with
| (lbs5, e22) -> begin
((

let uu____14968 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____14968 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____14969 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____14969), (cres), (FStar_TypeChecker_Rel.trivial_guard)));
)
end))))))
end))
end))
end))
end))
end
| uu____14982 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____15014 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____15014) with
| (lbs1, e21) -> begin
(

let uu____15033 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____15033) with
| (env0, topt) -> begin
(

let uu____15052 = (build_let_rec_env false env0 lbs1)
in (match (uu____15052) with
| (lbs2, rec_env) -> begin
(

let uu____15071 = (check_let_recs rec_env lbs2)
in (match (uu____15071) with
| (lbs3, g_lbs) -> begin
(

let uu____15090 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___102_15113 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___102_15113.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_15113.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___103_15115 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___103_15115.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___103_15115.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___103_15115.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___103_15115.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___103_15115.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___103_15115.FStar_Syntax_Syntax.lbpos})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____15090) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____15142 = (tc_term env2 e21)
in (match (uu____15142) with
| (e22, cres, g2) -> begin
(

let cres1 = (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e22 cres)
in (

let cres2 = (FStar_Syntax_Util.lcomp_set_flags cres1 ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
in (

let guard = (

let uu____15161 = (

let uu____15162 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Rel.close_guard env2 uu____15162 g2))
in (FStar_TypeChecker_Rel.conj_guard g_lbs uu____15161))
in (

let cres3 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres2)
in (

let tres = (norm env2 cres3.FStar_Syntax_Syntax.res_typ)
in (

let cres4 = (

let uu___104_15166 = cres3
in {FStar_Syntax_Syntax.eff_name = uu___104_15166.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___104_15166.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___104_15166.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____15167 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____15167) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____15203) -> begin
((e), (cres4), (guard))
end
| FStar_Pervasives_Native.None -> begin
(

let tres1 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (

let cres5 = (

let uu___105_15208 = cres4
in {FStar_Syntax_Syntax.eff_name = uu___105_15208.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___105_15208.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___105_15208.FStar_Syntax_Syntax.comp_thunk})
in ((e), (cres5), (guard))))
end))
end))))))))
end)))
end))
end))
end))
end))
end))
end
| uu____15211 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let uu____15240 = (FStar_Options.ml_ish ())
in (match (uu____15240) with
| true -> begin
false
end
| uu____15241 -> begin
(

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____15243 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____15243) with
| (formals, c) -> begin
(

let uu____15268 = (FStar_Syntax_Util.abs_formals lbdef)
in (match (uu____15268) with
| (actuals, uu____15278, uu____15279) -> begin
(match ((((FStar_List.length formals) < (Prims.parse_int "1")) || ((FStar_List.length actuals) < (Prims.parse_int "1")))) with
| true -> begin
(

let uu____15292 = (

let uu____15297 = (

let uu____15298 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____15299 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____15298 uu____15299)))
in ((FStar_Errors.Fatal_RecursiveFunctionLiteral), (uu____15297)))
in (FStar_Errors.raise_error uu____15292 lbtyp.FStar_Syntax_Syntax.pos))
end
| uu____15300 -> begin
(

let actuals1 = (

let uu____15302 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____15302 actuals))
in ((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____15322 -> begin
(

let uu____15323 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____15323))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____15340 -> begin
(

let uu____15341 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____15341))
end))
in (

let msg = (

let uu____15349 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____15350 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____15349 uu____15350 formals_msg actuals_msg)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_LetRecArgumentMismatch), (msg)) lbdef.FStar_Syntax_Syntax.pos))))
end
| uu____15351 -> begin
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

let uu____15357 = (FStar_List.fold_left (fun uu____15383 lb -> (match (uu____15383) with
| (lbs1, env1) -> begin
(

let uu____15403 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____15403) with
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
| uu____15422 -> begin
(

let uu____15423 = (

let uu____15430 = (

let uu____15431 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15431))
in (tc_check_tot_or_gtot_term (

let uu___106_15442 = env0
in {FStar_TypeChecker_Env.solver = uu___106_15442.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___106_15442.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___106_15442.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___106_15442.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___106_15442.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___106_15442.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___106_15442.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___106_15442.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___106_15442.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___106_15442.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___106_15442.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___106_15442.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___106_15442.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___106_15442.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___106_15442.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___106_15442.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___106_15442.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___106_15442.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___106_15442.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___106_15442.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___106_15442.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___106_15442.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___106_15442.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___106_15442.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___106_15442.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___106_15442.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___106_15442.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___106_15442.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___106_15442.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___106_15442.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___106_15442.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___106_15442.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___106_15442.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___106_15442.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___106_15442.FStar_TypeChecker_Env.dep_graph}) t uu____15430))
in (match (uu____15423) with
| (t1, uu____15444, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((

let uu____15448 = (FStar_TypeChecker_Rel.discharge_guard env2 g1)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____15448));
(norm env0 t1);
))
end))
end)
in (

let env3 = (

let uu____15450 = (termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1)
in (match (uu____15450) with
| true -> begin
(

let uu___107_15451 = env2
in {FStar_TypeChecker_Env.solver = uu___107_15451.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___107_15451.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___107_15451.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___107_15451.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___107_15451.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___107_15451.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___107_15451.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___107_15451.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___107_15451.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___107_15451.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___107_15451.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___107_15451.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1), (univ_vars1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___107_15451.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___107_15451.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___107_15451.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___107_15451.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___107_15451.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___107_15451.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___107_15451.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___107_15451.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___107_15451.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___107_15451.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___107_15451.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___107_15451.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___107_15451.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___107_15451.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___107_15451.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___107_15451.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___107_15451.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___107_15451.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___107_15451.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___107_15451.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___107_15451.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___107_15451.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___107_15451.FStar_TypeChecker_Env.dep_graph})
end
| uu____15466 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname ((univ_vars1), (t1)))
end))
in (

let lb1 = (

let uu___108_15468 = lb
in {FStar_Syntax_Syntax.lbname = uu___108_15468.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___108_15468.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___108_15468.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___108_15468.FStar_Syntax_Syntax.lbpos})
in (((lb1)::lbs1), (env3)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____15357) with
| (lbs1, env1) -> begin
(((FStar_List.rev lbs1)), (env1))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____15491 = (

let uu____15500 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____15526 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____15526) with
| (bs, t, lcomp) -> begin
(match (bs) with
| [] -> begin
(

let uu____15554 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_RecursiveFunctionLiteral), ("Only function literals may be defined recursively")) uu____15554))
end
| uu____15559 -> begin
(

let lb1 = (

let uu___109_15562 = lb
in (

let uu____15563 = (FStar_Syntax_Util.abs bs t lcomp)
in {FStar_Syntax_Syntax.lbname = uu___109_15562.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___109_15562.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___109_15562.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___109_15562.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____15563; FStar_Syntax_Syntax.lbattrs = uu___109_15562.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___109_15562.FStar_Syntax_Syntax.lbpos}))
in (

let uu____15566 = (

let uu____15573 = (FStar_TypeChecker_Env.set_expected_typ env lb1.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____15573 lb1.FStar_Syntax_Syntax.lbdef))
in (match (uu____15566) with
| (e, c, g) -> begin
((

let uu____15582 = (

let uu____15583 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____15583)))
in (match (uu____15582) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedGTotForLetRec), ("Expected let rec to be a Tot term; got effect GTot")) e.FStar_Syntax_Syntax.pos)
end
| uu____15584 -> begin
()
end));
(

let lb2 = (FStar_Syntax_Util.mk_letbinding lb1.FStar_Syntax_Syntax.lbname lb1.FStar_Syntax_Syntax.lbunivs lb1.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e lb1.FStar_Syntax_Syntax.lbattrs lb1.FStar_Syntax_Syntax.lbpos)
in ((lb2), (g)));
)
end)))
end)
end)))))
in (FStar_All.pipe_right uu____15500 FStar_List.unzip))
in (match (uu____15491) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____15632 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____15632) with
| (env1, uu____15650) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____15658 = (check_lbtyp top_level env lb)
in (match (uu____15658) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (Prims.op_disEquality univ_vars1 []))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UniversePolymorphicInnerLetBound), ("Inner let-bound definitions cannot be universe polymorphic")) e1.FStar_Syntax_Syntax.pos)
end
| uu____15697 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____15708 = (tc_maybe_toplevel_term (

let uu___110_15717 = env11
in {FStar_TypeChecker_Env.solver = uu___110_15717.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___110_15717.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___110_15717.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___110_15717.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___110_15717.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___110_15717.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___110_15717.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___110_15717.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___110_15717.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___110_15717.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___110_15717.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___110_15717.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___110_15717.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___110_15717.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___110_15717.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___110_15717.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___110_15717.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___110_15717.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___110_15717.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___110_15717.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___110_15717.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___110_15717.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___110_15717.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___110_15717.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___110_15717.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___110_15717.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___110_15717.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___110_15717.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___110_15717.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___110_15717.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___110_15717.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___110_15717.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___110_15717.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___110_15717.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___110_15717.FStar_TypeChecker_Env.dep_graph}) e11)
in (match (uu____15708) with
| (e12, c1, g1) -> begin
(

let uu____15731 = (

let uu____15736 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____15740 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____15736 e12 c1 wf_annot))
in (match (uu____15731) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____15755 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____15755) with
| true -> begin
(

let uu____15756 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____15757 = (FStar_Syntax_Print.lcomp_to_string c11)
in (

let uu____15758 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked let-bound def %s : %s guard is %s\n" uu____15756 uu____15757 uu____15758))))
end
| uu____15759 -> begin
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

let uu____15792 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____15792) with
| (univ_opening, univ_vars1) -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (env))
end))
end
| uu____15831 -> begin
(

let uu____15832 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____15832) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____15881 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____15881)))
end
| uu____15888 -> begin
(

let uu____15889 = (FStar_Syntax_Util.type_u ())
in (match (uu____15889) with
| (k, uu____15909) -> begin
(

let uu____15910 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____15910) with
| (t2, uu____15932, g) -> begin
((

let uu____15935 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____15935) with
| true -> begin
(

let uu____15936 = (

let uu____15937 = (FStar_Syntax_Util.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____15937))
in (

let uu____15938 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____15936 uu____15938)))
end
| uu____15939 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____15941 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____15941))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____15949 -> (match (uu____15949) with
| (x, imp) -> begin
(

let uu____15968 = (FStar_Syntax_Util.type_u ())
in (match (uu____15968) with
| (tu, u) -> begin
((

let uu____15988 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____15988) with
| true -> begin
(

let uu____15989 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____15990 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____15991 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____15989 uu____15990 uu____15991))))
end
| uu____15992 -> begin
()
end));
(

let uu____15993 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____15993) with
| (t, uu____16013, g) -> begin
(

let x1 = (((

let uu___111_16021 = x
in {FStar_Syntax_Syntax.ppname = uu___111_16021.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___111_16021.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____16023 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____16023) with
| true -> begin
(

let uu____16024 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____16025 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____16024 uu____16025)))
end
| uu____16026 -> begin
()
end));
(

let uu____16027 = (push_binding env x1)
in ((x1), (uu____16027), (g), (u)));
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

let uu____16117 = (tc_binder env1 b)
in (match (uu____16117) with
| (b1, env', g, u) -> begin
(

let uu____16158 = (aux env' bs2)
in (match (uu____16158) with
| (bs3, env'1, g', us) -> begin
(

let uu____16211 = (

let uu____16212 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____16212))
in (((b1)::bs3), (env'1), (uu____16211), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____16297 uu____16298 -> (match (((uu____16297), (uu____16298))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____16367 = (tc_term env1 t)
in (match (uu____16367) with
| (t1, uu____16385, g') -> begin
(

let uu____16387 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____16387)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____16429 -> (match (uu____16429) with
| (pats1, g) -> begin
(

let uu____16454 = (tc_args env p)
in (match (uu____16454) with
| (args, g') -> begin
(

let uu____16467 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats1), (uu____16467)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____16480 = (tc_maybe_toplevel_term env e)
in (match (uu____16480) with
| (e1, c, g) -> begin
(

let uu____16496 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____16496) with
| true -> begin
((e1), (c), (g))
end
| uu____16503 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (FStar_Syntax_Syntax.lcomp_comp c)
in (

let c2 = (norm_c env c1)
in (

let uu____16507 = (

let uu____16512 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____16512) with
| true -> begin
(

let uu____16517 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____16517), (false)))
end
| uu____16518 -> begin
(

let uu____16519 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____16519), (true)))
end))
in (match (uu____16507) with
| (target_comp, allow_ghost) -> begin
(

let uu____16528 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____16528) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____16538 = (FStar_Syntax_Util.lcomp_of_comp target_comp)
in (

let uu____16539 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in ((e1), (uu____16538), (uu____16539))))
end
| uu____16540 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____16549 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in (FStar_Errors.raise_error uu____16549 e1.FStar_Syntax_Syntax.pos))
end
| uu____16560 -> begin
(

let uu____16561 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in (FStar_Errors.raise_error uu____16561 e1.FStar_Syntax_Syntax.pos))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____16584 = (tc_tot_or_gtot_term env t)
in (match (uu____16584) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____16612 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____16612) with
| true -> begin
(

let uu____16613 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____16613))
end
| uu____16614 -> begin
()
end));
(

let env1 = (

let uu___112_16616 = env
in {FStar_TypeChecker_Env.solver = uu___112_16616.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___112_16616.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___112_16616.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___112_16616.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___112_16616.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___112_16616.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___112_16616.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___112_16616.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___112_16616.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___112_16616.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___112_16616.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___112_16616.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___112_16616.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___112_16616.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___112_16616.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___112_16616.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___112_16616.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___112_16616.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___112_16616.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___112_16616.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___112_16616.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___112_16616.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___112_16616.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___112_16616.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___112_16616.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___112_16616.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___112_16616.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___112_16616.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___112_16616.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___112_16616.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___112_16616.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___112_16616.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___112_16616.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___112_16616.FStar_TypeChecker_Env.dep_graph})
in (

let uu____16623 = (FStar_All.try_with (fun uu___114_16637 -> (match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)) (fun uu___113_16649 -> (match (uu___113_16649) with
| FStar_Errors.Error (e1, msg, uu____16658) -> begin
(

let uu____16659 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((e1), (msg)) uu____16659))
end)))
in (match (uu____16623) with
| (t, c, g) -> begin
(

let uu____16675 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____16675) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____16684 -> begin
(

let uu____16685 = (

let uu____16690 = (

let uu____16691 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____16691))
in ((FStar_Errors.Fatal_UnexpectedImplictArgument), (uu____16690)))
in (

let uu____16692 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____16685 uu____16692)))
end))
end)));
))


let level_of_type_fail : 'Auu____16703 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  'Auu____16703 = (fun env e t -> (

let uu____16716 = (

let uu____16721 = (

let uu____16722 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____16722 t))
in ((FStar_Errors.Fatal_UnexpectedTermType), (uu____16721)))
in (

let uu____16723 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____16716 uu____16723))))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____16740 = (

let uu____16741 = (FStar_Syntax_Util.unrefine t1)
in uu____16741.FStar_Syntax_Syntax.n)
in (match (uu____16740) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____16745 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____16747 -> begin
(

let uu____16748 = (FStar_Syntax_Util.type_u ())
in (match (uu____16748) with
| (t_u, u) -> begin
(

let env1 = (

let uu___115_16756 = env
in {FStar_TypeChecker_Env.solver = uu___115_16756.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___115_16756.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___115_16756.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___115_16756.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___115_16756.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___115_16756.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___115_16756.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___115_16756.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___115_16756.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___115_16756.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___115_16756.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___115_16756.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___115_16756.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___115_16756.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___115_16756.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___115_16756.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___115_16756.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___115_16756.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___115_16756.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___115_16756.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___115_16756.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___115_16756.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___115_16756.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___115_16756.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___115_16756.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___115_16756.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___115_16756.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___115_16756.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___115_16756.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___115_16756.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___115_16756.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___115_16756.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___115_16756.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___115_16756.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___115_16756.FStar_TypeChecker_Env.dep_graph})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____16760 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____16760))
end
| uu____16761 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____16770 = (

let uu____16771 = (FStar_Syntax_Subst.compress e)
in uu____16771.FStar_Syntax_Syntax.n)
in (match (uu____16770) with
| FStar_Syntax_Syntax.Tm_bvar (uu____16776) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____16781) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____16808) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____16824) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____16847, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____16874) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____16881 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____16881) with
| ((uu____16892, t), uu____16894) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____16900 = (FStar_Syntax_Util.unfold_lazy i)
in (universe_of_aux env uu____16900))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____16901, (FStar_Util.Inl (t), uu____16903), uu____16904) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____16951, (FStar_Util.Inr (c), uu____16953), uu____16954) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____17002) -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant env e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____17011; FStar_Syntax_Syntax.vars = uu____17012}, us) -> begin
(

let uu____17018 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17018) with
| ((us', t), uu____17031) -> begin
((match ((Prims.op_disEquality (FStar_List.length us) (FStar_List.length us'))) with
| true -> begin
(

let uu____17037 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), ("Unexpected number of universe instantiations")) uu____17037))
end
| uu____17038 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____17053 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____17054) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____17064) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____17087 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____17087) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____17107 -> (match (uu____17107) with
| (b, uu____17113) -> begin
(

let uu____17114 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____17114))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____17119 = (universe_of_aux env res)
in (level_of_type env res uu____17119)))
in (

let u_c = (

let uu____17121 = (FStar_TypeChecker_Env.effect_repr env c1 u_res)
in (match (uu____17121) with
| FStar_Pervasives_Native.None -> begin
u_res
end
| FStar_Pervasives_Native.Some (trepr) -> begin
(

let uu____17125 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____17125))
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
| FStar_Syntax_Syntax.Tm_bvar (uu____17218) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____17233) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____17272) -> begin
(

let uu____17273 = (universe_of_aux env hd3)
in ((uu____17273), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____17286) -> begin
(

let uu____17287 = (universe_of_aux env hd3)
in ((uu____17287), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____17300) -> begin
(

let uu____17317 = (universe_of_aux env hd3)
in ((uu____17317), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____17330) -> begin
(

let uu____17337 = (universe_of_aux env hd3)
in ((uu____17337), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____17350) -> begin
(

let uu____17377 = (universe_of_aux env hd3)
in ((uu____17377), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____17390) -> begin
(

let uu____17397 = (universe_of_aux env hd3)
in ((uu____17397), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____17410) -> begin
(

let uu____17411 = (universe_of_aux env hd3)
in ((uu____17411), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____17424) -> begin
(

let uu____17437 = (universe_of_aux env hd3)
in ((uu____17437), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____17450) -> begin
(

let uu____17457 = (universe_of_aux env hd3)
in ((uu____17457), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____17470) -> begin
(

let uu____17471 = (universe_of_aux env hd3)
in ((uu____17471), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____17484, (hd4)::uu____17486) -> begin
(

let uu____17551 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____17551) with
| (uu____17566, uu____17567, hd5) -> begin
(

let uu____17585 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____17585) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____17636 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____17638 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____17638) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____17689 -> begin
(

let uu____17690 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____17690) with
| (env1, uu____17712) -> begin
(

let env2 = (

let uu___116_17718 = env1
in {FStar_TypeChecker_Env.solver = uu___116_17718.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___116_17718.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___116_17718.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___116_17718.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___116_17718.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___116_17718.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___116_17718.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___116_17718.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___116_17718.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___116_17718.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___116_17718.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___116_17718.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___116_17718.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___116_17718.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___116_17718.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___116_17718.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___116_17718.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___116_17718.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___116_17718.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___116_17718.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___116_17718.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___116_17718.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___116_17718.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___116_17718.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___116_17718.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___116_17718.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___116_17718.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___116_17718.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___116_17718.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___116_17718.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___116_17718.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___116_17718.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___116_17718.FStar_TypeChecker_Env.dep_graph})
in ((

let uu____17720 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____17720) with
| true -> begin
(

let uu____17721 = (

let uu____17722 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____17722))
in (

let uu____17723 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____17721 uu____17723)))
end
| uu____17724 -> begin
()
end));
(

let uu____17725 = (tc_term env2 hd3)
in (match (uu____17725) with
| (uu____17746, {FStar_Syntax_Syntax.eff_name = uu____17747; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____17749; FStar_Syntax_Syntax.comp_thunk = uu____17750}, g) -> begin
((

let uu____17769 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____17769 FStar_Pervasives.ignore));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____17780 = (type_of_head true hd1 args)
in (match (uu____17780) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____17820 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____17820) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____17863 -> begin
(

let uu____17864 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____17864))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____17867, (hd1)::uu____17869) -> begin
(

let uu____17934 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____17934) with
| (uu____17937, uu____17938, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____17956, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____17999 = (universe_of_aux env e)
in (level_of_type env e uu____17999)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____18018 = (tc_binders env tps)
in (match (uu____18018) with
| (tps1, env1, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
((tps1), (env1), (us));
)
end)))


let rec type_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env t -> (

let mk_tm_type = (fun u -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____18062 = (

let uu____18063 = (FStar_Syntax_Subst.compress t)
in uu____18063.FStar_Syntax_Syntax.n)
in (match (uu____18062) with
| FStar_Syntax_Syntax.Tm_delayed (uu____18068) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____18095) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____18102 = (FStar_Syntax_Util.unfold_lazy i)
in (type_of_well_typed_term env uu____18102))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____18104 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env [] fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____18104 (fun uu____18118 -> (match (uu____18118) with
| (t1, uu____18126) -> begin
FStar_Pervasives_Native.Some (t1)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____18128; FStar_Syntax_Syntax.vars = uu____18129}, us) -> begin
(

let uu____18135 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env us fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____18135 (fun uu____18149 -> (match (uu____18149) with
| (t1, uu____18157) -> begin
FStar_Pervasives_Native.Some (t1)
end))))
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(

let uu____18159 = (tc_constant env t.FStar_Syntax_Syntax.pos sc)
in FStar_Pervasives_Native.Some (uu____18159))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____18161 = (mk_tm_type (FStar_Syntax_Syntax.U_succ (u)))
in FStar_Pervasives_Native.Some (uu____18161))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = eff; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (tbody); FStar_Syntax_Syntax.residual_flags = uu____18170})) -> begin
(

let mk_comp = (match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_Total')
end
| uu____18218 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_GTotal')
end
| uu____18233 -> begin
FStar_Pervasives_Native.None
end)
end)
in (FStar_Util.bind_opt mk_comp (fun f -> (

let uu____18257 = (universe_of_well_typed_term env tbody)
in (FStar_Util.bind_opt uu____18257 (fun u -> (

let uu____18265 = (

let uu____18268 = (

let uu____18271 = (

let uu____18272 = (

let uu____18285 = (f tbody (FStar_Pervasives_Native.Some (u)))
in ((bs), (uu____18285)))
in FStar_Syntax_Syntax.Tm_arrow (uu____18272))
in (FStar_Syntax_Syntax.mk uu____18271))
in (uu____18268 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in FStar_Pervasives_Native.Some (uu____18265))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____18315 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____18315) with
| (bs1, c1) -> begin
(

let rec aux = (fun env1 us bs2 -> (match (bs2) with
| [] -> begin
(

let uu____18362 = (universe_of_well_typed_term env1 (FStar_Syntax_Util.comp_result c1))
in (FStar_Util.bind_opt uu____18362 (fun uc -> (

let uu____18370 = (mk_tm_type (FStar_Syntax_Syntax.U_max ((uc)::us)))
in FStar_Pervasives_Native.Some (uu____18370)))))
end
| ((x, imp))::bs3 -> begin
(

let uu____18388 = (universe_of_well_typed_term env1 x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____18388 (fun u_x -> (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x)
in (aux env2 ((u_x)::us) bs3)))))
end))
in (aux env [] bs1))
end))
end
| FStar_Syntax_Syntax.Tm_abs (uu____18397) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____18415) -> begin
(

let uu____18420 = (universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____18420 (fun u_x -> (

let uu____18428 = (mk_tm_type u_x)
in FStar_Pervasives_Native.Some (uu____18428)))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let t_hd = (type_of_well_typed_term env hd1)
in (

let rec aux = (fun t_hd1 -> (

let uu____18464 = (

let uu____18465 = (FStar_TypeChecker_Normalize.unfold_whnf env t_hd1)
in uu____18465.FStar_Syntax_Syntax.n)
in (match (uu____18464) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_bs = (FStar_List.length bs)
in (

let bs_t_opt = (match ((n_args < n_bs)) with
| true -> begin
(

let uu____18527 = (FStar_Util.first_N n_args bs)
in (match (uu____18527) with
| (bs1, rest) -> begin
(

let t1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None t_hd1.FStar_Syntax_Syntax.pos)
in (

let uu____18597 = (

let uu____18602 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Subst.open_comp bs1 uu____18602))
in (match (uu____18597) with
| (bs2, c1) -> begin
FStar_Pervasives_Native.Some (((bs2), ((FStar_Syntax_Util.comp_result c1))))
end)))
end))
end
| uu____18621 -> begin
(match ((Prims.op_Equality n_args n_bs)) with
| true -> begin
(

let uu____18638 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____18638) with
| (bs1, c1) -> begin
(

let uu____18653 = (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
in (match (uu____18653) with
| true -> begin
FStar_Pervasives_Native.Some (((bs1), ((FStar_Syntax_Util.comp_result c1))))
end
| uu____18670 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| uu____18677 -> begin
FStar_Pervasives_Native.None
end)
end)
in (FStar_Util.bind_opt bs_t_opt (fun uu____18695 -> (match (uu____18695) with
| (bs1, t1) -> begin
(

let subst1 = (FStar_List.map2 (fun b a -> FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), ((FStar_Pervasives_Native.fst a))))) bs1 args)
in (

let uu____18741 = (FStar_Syntax_Subst.subst subst1 t1)
in FStar_Pervasives_Native.Some (uu____18741)))
end))))))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____18743) -> begin
(aux x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____18749, uu____18750) -> begin
(aux t1)
end
| uu____18791 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_Util.bind_opt t_hd aux)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____18792, (FStar_Util.Inl (t1), uu____18794), uu____18795) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____18844, (FStar_Util.Inr (c), uu____18846), uu____18847) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____18896, t1) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.t_term)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____18931) -> begin
(type_of_well_typed_term env t1)
end
| FStar_Syntax_Syntax.Tm_match (uu____18936) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____18959) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (uu____18972) -> begin
FStar_Pervasives_Native.None
end))))
and universe_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun env t -> (

let uu____18983 = (type_of_well_typed_term env t)
in (match (uu____18983) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.pos = uu____18989; FStar_Syntax_Syntax.vars = uu____18990}) -> begin
FStar_Pervasives_Native.Some (u)
end
| uu____18995 -> begin
FStar_Pervasives_Native.None
end)))


let check_type_of_well_typed_term : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun must_total env t k -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let env2 = (

let uu___117_19012 = env1
in {FStar_TypeChecker_Env.solver = uu___117_19012.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_19012.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_19012.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_19012.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_19012.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_19012.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_19012.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_19012.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_19012.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_19012.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_19012.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_19012.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_19012.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___117_19012.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___117_19012.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___117_19012.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___117_19012.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_19012.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___117_19012.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___117_19012.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___117_19012.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___117_19012.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___117_19012.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___117_19012.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_19012.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___117_19012.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___117_19012.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___117_19012.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___117_19012.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___117_19012.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___117_19012.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___117_19012.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___117_19012.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___117_19012.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___117_19012.FStar_TypeChecker_Env.dep_graph})
in (

let slow_check = (fun uu____19016 -> (match (must_total) with
| true -> begin
(

let uu____19017 = (env2.FStar_TypeChecker_Env.type_of env2 t)
in (match (uu____19017) with
| (uu____19024, uu____19025, g) -> begin
g
end))
end
| uu____19027 -> begin
(

let uu____19028 = (env2.FStar_TypeChecker_Env.tc_term env2 t)
in (match (uu____19028) with
| (uu____19035, uu____19036, g) -> begin
g
end))
end))
in (

let uu____19038 = (

let uu____19039 = (FStar_Options.__temp_fast_implicits ())
in (FStar_All.pipe_left Prims.op_Negation uu____19039))
in (match (uu____19038) with
| true -> begin
(slow_check ())
end
| uu____19040 -> begin
(

let uu____19041 = (type_of_well_typed_term env2 t)
in (match (uu____19041) with
| FStar_Pervasives_Native.None -> begin
(slow_check ())
end
| FStar_Pervasives_Native.Some (k') -> begin
((

let uu____19046 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____19046) with
| true -> begin
(

let uu____19047 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____19048 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____19049 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____19050 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n" uu____19047 uu____19048 uu____19049 uu____19050)))))
end
| uu____19051 -> begin
()
end));
(

let b = (FStar_TypeChecker_Rel.subtype_nosmt env2 k' k)
in ((

let uu____19054 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____19054) with
| true -> begin
(

let uu____19055 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____19056 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____19057 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____19058 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n" uu____19055 (match (b) with
| true -> begin
"succeeded"
end
| uu____19059 -> begin
"failed"
end) uu____19056 uu____19057 uu____19058)))))
end
| uu____19060 -> begin
()
end));
(match (b) with
| true -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____19061 -> begin
(slow_check ())
end);
));
)
end))
end))))))




