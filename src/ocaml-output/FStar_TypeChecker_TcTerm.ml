
open Prims
open FStar_Pervasives

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___119_5 = env
in {FStar_TypeChecker_Env.solver = uu___119_5.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_5.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_5.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_5.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_5.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_5.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_5.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_5.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_5.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___119_5.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_5.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_5.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_5.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_5.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_5.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_5.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_5.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___119_5.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___119_5.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___119_5.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___119_5.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___119_5.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___119_5.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_5.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_5.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_5.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___119_5.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___119_5.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___119_5.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___119_5.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___119_5.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___119_5.FStar_TypeChecker_Env.dsenv}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___120_10 = env
in {FStar_TypeChecker_Env.solver = uu___120_10.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___120_10.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___120_10.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___120_10.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___120_10.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___120_10.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___120_10.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___120_10.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___120_10.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___120_10.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___120_10.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___120_10.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___120_10.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___120_10.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___120_10.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___120_10.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___120_10.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___120_10.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___120_10.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___120_10.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___120_10.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___120_10.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___120_10.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___120_10.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___120_10.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___120_10.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___120_10.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___120_10.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___120_10.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___120_10.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___120_10.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___120_10.FStar_TypeChecker_Env.dsenv}))


let mk_lex_list : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v1 tl1 -> (

let r = (match ((Prims.op_Equality tl1.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
v1.FStar_Syntax_Syntax.pos
end
| uu____42 -> begin
(FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos tl1.FStar_Syntax_Syntax.pos)
end)
in (

let uu____43 = (

let uu____44 = (

let uu____45 = (FStar_Syntax_Syntax.as_arg v1)
in (

let uu____46 = (

let uu____49 = (FStar_Syntax_Syntax.as_arg tl1)
in (uu____49)::[])
in (uu____45)::uu____46))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____44))
in (uu____43 FStar_Pervasives_Native.None r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___114_57 -> (match (uu___114_57) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____60 -> begin
false
end))


let steps : 'Auu____67 . 'Auu____67  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[])


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
t
end
| uu____121 -> begin
(

let t1 = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____125 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t1)
in (

let uu____129 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____129) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t1)
end
| uu____135 -> begin
(

let fail = (fun uu____139 -> (

let msg = (match (head_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____141 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" uu____141))
end
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____143 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____144 = (FStar_TypeChecker_Normalize.term_to_string env head1)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" uu____143 uu____144)))
end)
in (

let uu____145 = (

let uu____146 = (

let uu____151 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____151)))
in FStar_Errors.Error (uu____146))
in (FStar_Exn.raise uu____145))))
in (

let s = (

let uu____153 = (

let uu____154 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____154))
in (FStar_TypeChecker_Util.new_uvar env uu____153))
in (

let uu____163 = (FStar_TypeChecker_Rel.try_teq true env t1 s)
in (match (uu____163) with
| FStar_Pervasives_Native.Some (g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
s;
)
end
| uu____168 -> begin
(fail ())
end))))
end)
end))))
end))
in (aux false kt)))


let push_binding : 'Auu____177 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____177)  ->  FStar_TypeChecker_Env.env = (fun env b -> (FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v1 -> (

let uu____210 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____210) with
| true -> begin
s
end
| uu____211 -> begin
(FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), (v1))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let uu___121_226 = lc
in {FStar_Syntax_Syntax.eff_name = uu___121_226.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___121_226.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____229 -> (

let uu____230 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ uu____230 t)))}))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> e)


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (

let uu____281 = (

let uu____282 = (FStar_Syntax_Subst.compress t)
in uu____282.FStar_Syntax_Syntax.n)
in (match (uu____281) with
| FStar_Syntax_Syntax.Tm_arrow (uu____285, c) -> begin
(

let uu____303 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c))
in (match (uu____303) with
| true -> begin
(

let t1 = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (

let uu____305 = (

let uu____306 = (FStar_Syntax_Subst.compress t1)
in uu____306.FStar_Syntax_Syntax.n)
in (match (uu____305) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____310) -> begin
false
end
| uu____311 -> begin
true
end)))
end
| uu____312 -> begin
false
end))
end
| uu____313 -> begin
true
end)))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____316 = (

let uu____319 = ((

let uu____322 = (should_return t)
in (not (uu____322))) || (

let uu____324 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____324))))
in (match (uu____319) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____327 -> begin
(FStar_TypeChecker_Util.return_value env t e)
end))
in (FStar_Syntax_Util.lcomp_of_comp uu____316))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____332 = (

let uu____339 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____339) with
| FStar_Pervasives_Native.None -> begin
(((memo_tk e t)), (lc), (guard))
end
| FStar_Pervasives_Native.Some (t') -> begin
((

let uu____350 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____350) with
| true -> begin
(

let uu____351 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____352 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" uu____351 uu____352)))
end
| uu____353 -> begin
()
end));
(

let uu____354 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____354) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____370 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____370) with
| (e2, g) -> begin
((

let uu____384 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____384) with
| true -> begin
(

let uu____385 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____386 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____387 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____388 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____385 uu____386 uu____387 uu____388)))))
end
| uu____389 -> begin
()
end));
(

let msg = (

let uu____395 = (FStar_TypeChecker_Rel.is_trivial g)
in (match (uu____395) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____402 -> begin
(FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____412 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc1 g1)
in (match (uu____412) with
| (lc2, g2) -> begin
(((memo_tk e2 t')), ((set_lcomp_result lc2 t')), (g2))
end))));
)
end)))
end));
)
end))
in (match (uu____332) with
| (e1, lc1, g) -> begin
((

let uu____435 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____435) with
| true -> begin
(

let uu____436 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (FStar_Util.print1 "Return comp type is %s\n" uu____436))
end
| uu____437 -> begin
()
end));
((e1), (lc1), (g));
)
end))))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____462 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____462) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____472 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____472) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt uu____508 -> (match (uu____508) with
| (e, c) -> begin
(

let tot_or_gtot = (fun c1 -> (

let uu____537 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____537) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c1))
end
| uu____538 -> begin
(

let uu____539 = (FStar_Syntax_Util.is_pure_or_ghost_comp c1)
in (match (uu____539) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c1))
end
| uu____540 -> begin
(failwith "Impossible: Expected pure_or_ghost comp")
end))
end)))
in (

let uu____541 = (match (copt) with
| FStar_Pervasives_Native.Some (uu____554) -> begin
((copt), (c))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____557 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Parser_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____559 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____559)))))
in (match (uu____557) with
| true -> begin
(

let uu____566 = (

let uu____569 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____569))
in ((uu____566), (c)))
end
| uu____572 -> begin
(

let uu____573 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____573) with
| true -> begin
(

let uu____580 = (tot_or_gtot c)
in ((FStar_Pervasives_Native.None), (uu____580)))
end
| uu____583 -> begin
(

let uu____584 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____584) with
| true -> begin
(

let uu____591 = (

let uu____594 = (tot_or_gtot c)
in FStar_Pervasives_Native.Some (uu____594))
in ((uu____591), (c)))
end
| uu____597 -> begin
((FStar_Pervasives_Native.None), (c))
end))
end))
end))
end)
in (match (uu____541) with
| (expected_c_opt, c1) -> begin
(

let c2 = (norm_c env c1)
in (match (expected_c_opt) with
| FStar_Pervasives_Native.None -> begin
((e), (c2), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (expected_c) -> begin
(

let uu____620 = (FStar_TypeChecker_Util.check_comp env e c2 expected_c)
in (match (uu____620) with
| (e1, uu____634, g) -> begin
(

let g1 = (

let uu____637 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____637 "could not prove post-condition" g))
in ((

let uu____639 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____639) with
| true -> begin
(

let uu____640 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____641 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" uu____640 uu____641)))
end
| uu____642 -> begin
()
end));
(

let e2 = (FStar_TypeChecker_Util.maybe_lift env e1 (FStar_Syntax_Util.comp_effect_name c2) (FStar_Syntax_Util.comp_effect_name expected_c) (FStar_Syntax_Util.comp_result c2))
in ((e2), (expected_c), (g1)));
))
end))
end))
end)))
end))


let no_logical_guard : 'Auu____652 'Auu____653 . FStar_TypeChecker_Env.env  ->  ('Auu____653 * 'Auu____652 * FStar_TypeChecker_Env.guard_t)  ->  ('Auu____653 * 'Auu____652 * FStar_TypeChecker_Env.guard_t) = (fun env uu____673 -> (match (uu____673) with
| (te, kt, f) -> begin
(

let uu____683 = (FStar_TypeChecker_Rel.guard_form f)
in (match (uu____683) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____691 = (

let uu____692 = (

let uu____697 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____698 = (FStar_TypeChecker_Env.get_range env)
in ((uu____697), (uu____698))))
in FStar_Errors.Error (uu____692))
in (FStar_Exn.raise uu____691))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let uu____709 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____709) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "Expected type is None\n")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____713 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____713))
end)))


let rec get_pat_vars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun pats acc -> (

let pats1 = (FStar_Syntax_Util.unmeta pats)
in (

let uu____737 = (FStar_Syntax_Util.head_and_args pats1)
in (match (uu____737) with
| (head1, args) -> begin
(

let uu____776 = (

let uu____777 = (FStar_Syntax_Util.un_uinst head1)
in uu____777.FStar_Syntax_Syntax.n)
in (match (uu____776) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
acc
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
(

let uu____784 = (FStar_List.tl args)
in (get_pat_vars_args uu____784 acc))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
(get_pat_vars_args args acc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(get_pat_vars_args args acc)
end
| uu____793 -> begin
(

let uu____794 = (FStar_Syntax_Free.names pats1)
in (FStar_Util.set_union acc uu____794))
end))
end))))
and get_pat_vars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun args acc -> (FStar_List.fold_left (fun s arg -> (get_pat_vars (FStar_Pervasives_Native.fst arg) s)) acc args))


let check_smt_pat : 'Auu____829 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * 'Auu____829) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.unit = (fun env t bs c -> (

let uu____862 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____862) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____863; FStar_Syntax_Syntax.effect_name = uu____864; FStar_Syntax_Syntax.result_typ = uu____865; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____869))::[]; FStar_Syntax_Syntax.flags = uu____870}) -> begin
(

let pat_vars = (

let uu____918 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (

let uu____919 = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
in (get_pat_vars uu____918 uu____919)))
in (

let uu____922 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____949 -> (match (uu____949) with
| (b, uu____955) -> begin
(

let uu____956 = (FStar_Util.set_mem b pat_vars)
in (not (uu____956)))
end))))
in (match (uu____922) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____962) -> begin
(

let uu____967 = (

let uu____968 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____968))
in (FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____967))
end)))
end
| uu____969 -> begin
(failwith "Impossible")
end)
end
| uu____970 -> begin
()
end)))


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (

let uu____999 = (

let uu____1000 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____1000)))
in (match (uu____999) with
| true -> begin
env.FStar_TypeChecker_Env.letrecs
end
| uu____1007 -> begin
(match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env1 = (

let uu___122_1031 = env
in {FStar_TypeChecker_Env.solver = uu___122_1031.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___122_1031.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___122_1031.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___122_1031.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___122_1031.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___122_1031.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___122_1031.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___122_1031.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___122_1031.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___122_1031.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___122_1031.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___122_1031.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___122_1031.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___122_1031.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___122_1031.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___122_1031.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___122_1031.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___122_1031.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___122_1031.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___122_1031.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___122_1031.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___122_1031.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___122_1031.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___122_1031.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___122_1031.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___122_1031.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___122_1031.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___122_1031.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___122_1031.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___122_1031.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___122_1031.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___122_1031.FStar_TypeChecker_Env.dsenv})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____1065 -> (match (uu____1065) with
| (b, uu____1073) -> begin
(

let t = (

let uu____1075 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____1075))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____1078) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1079) -> begin
[]
end
| uu____1092 -> begin
(

let uu____1093 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____1093)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____1098 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____1098) with
| (head1, uu____1114) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____1136 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____1140 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___115_1149 -> (match (uu___115_1149) with
| FStar_Syntax_Syntax.DECREASES (uu____1150) -> begin
true
end
| uu____1153 -> begin
false
end))))
in (match (uu____1140) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____1157 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____1166 -> begin
(mk_lex_list xs)
end))
end))))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____1183 -> (match (uu____1183) with
| (l, t) -> begin
(

let uu____1196 = (

let uu____1197 = (FStar_Syntax_Subst.compress t)
in uu____1197.FStar_Syntax_Syntax.n)
in (match (uu____1196) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____1256 -> (match (uu____1256) with
| (x, imp) -> begin
(

let uu____1267 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____1267) with
| true -> begin
(

let uu____1272 = (

let uu____1273 = (

let uu____1276 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____1276))
in (FStar_Syntax_Syntax.new_bv uu____1273 x.FStar_Syntax_Syntax.sort))
in ((uu____1272), (imp)))
end
| uu____1277 -> begin
((x), (imp))
end))
end))))
in (

let uu____1278 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____1278) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____1295 = (

let uu____1296 = (

let uu____1297 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____1298 = (

let uu____1301 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____1301)::[])
in (uu____1297)::uu____1298))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____1296))
in (uu____1295 FStar_Pervasives_Native.None r))
in (

let uu____1304 = (FStar_Util.prefix formals2)
in (match (uu____1304) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___123_1349 = last1
in (

let uu____1350 = (FStar_Syntax_Util.refine last1 precedes1)
in {FStar_Syntax_Syntax.ppname = uu___123_1349.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_1349.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1350}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____1376 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1376) with
| true -> begin
(

let uu____1377 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____1378 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1379 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____1377 uu____1378 uu____1379))))
end
| uu____1380 -> begin
()
end));
((l), (t'));
))))
end))))
end)))
end
| uu____1383 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let uu___124_1814 = env
in {FStar_TypeChecker_Env.solver = uu___124_1814.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___124_1814.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___124_1814.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___124_1814.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___124_1814.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___124_1814.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___124_1814.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___124_1814.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___124_1814.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___124_1814.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___124_1814.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___124_1814.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___124_1814.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___124_1814.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___124_1814.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___124_1814.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___124_1814.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___124_1814.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___124_1814.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___124_1814.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___124_1814.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___124_1814.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___124_1814.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___124_1814.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___124_1814.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___124_1814.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___124_1814.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___124_1814.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___124_1814.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___124_1814.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___124_1814.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___124_1814.FStar_TypeChecker_Env.dsenv}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (match ((Prims.op_Equality e.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____1824 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____1826 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1826) with
| true -> begin
(

let uu____1827 = (

let uu____1828 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1828))
in (

let uu____1829 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" uu____1827 uu____1829)))
end
| uu____1830 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1838) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1869) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1876) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1893) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____1894) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1895) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1896) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____1897) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1914) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____1927) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____1934) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____1935; FStar_Syntax_Syntax.vars = uu____1936}, FStar_Syntax_Syntax.Meta_alien (uu____1937, uu____1938, ty)) -> begin
(

let uu____1948 = (

let uu____1949 = (FStar_Syntax_Syntax.mk_Total ty)
in (FStar_All.pipe_right uu____1949 FStar_Syntax_Util.lcomp_of_comp))
in ((top), (uu____1948), (FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____1955 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____1955) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___125_1972 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___125_1972.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___125_1972.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___125_1972.FStar_TypeChecker_Env.implicits})
in ((e2), (c), (g1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____1989 = (FStar_Syntax_Util.type_u ())
in (match (uu____1989) with
| (t, u) -> begin
(

let uu____2002 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____2002) with
| (e2, c, g) -> begin
(

let uu____2018 = (

let uu____2033 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2033) with
| (env2, uu____2055) -> begin
(tc_pats env2 pats)
end))
in (match (uu____2018) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___126_2089 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___126_2089.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___126_2089.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___126_2089.FStar_TypeChecker_Env.implicits})
in (

let uu____2090 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2093 = (FStar_TypeChecker_Rel.conj_guard g g'1)
in ((uu____2090), (c), (uu____2093)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____2101 = (

let uu____2102 = (FStar_Syntax_Subst.compress e1)
in uu____2102.FStar_Syntax_Syntax.n)
in (match (uu____2101) with
| FStar_Syntax_Syntax.Tm_let ((uu____2111, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____2113; FStar_Syntax_Syntax.lbtyp = uu____2114; FStar_Syntax_Syntax.lbeff = uu____2115; FStar_Syntax_Syntax.lbdef = e11})::[]), e2) -> begin
(

let uu____2140 = (

let uu____2147 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (tc_term uu____2147 e11))
in (match (uu____2140) with
| (e12, c1, g1) -> begin
(

let uu____2157 = (tc_term env1 e2)
in (match (uu____2157) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e3 = (

let uu____2181 = (

let uu____2184 = (

let uu____2185 = (

let uu____2198 = (

let uu____2205 = (

let uu____2208 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_Syntax_Syntax.t_unit), (e13)))
in (uu____2208)::[])
in ((false), (uu____2205)))
in ((uu____2198), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____2185))
in (FStar_Syntax_Syntax.mk uu____2184))
in (uu____2181 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2230 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e5), (c), (uu____2230)))))))))
end))
end))
end
| uu____2233 -> begin
(

let uu____2234 = (tc_term env1 e1)
in (match (uu____2234) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____2256)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____2273 = (tc_term env1 e1)
in (match (uu____2273) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____2297) -> begin
(

let uu____2344 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2344) with
| (env0, uu____2358) -> begin
(

let uu____2363 = (tc_comp env0 expected_c)
in (match (uu____2363) with
| (expected_c1, uu____2377, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c1)
in (

let uu____2382 = (

let uu____2389 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____2389 e1))
in (match (uu____2382) with
| (e2, c', g') -> begin
(

let uu____2399 = (

let uu____2406 = (

let uu____2411 = (c'.FStar_Syntax_Syntax.comp ())
in ((e2), (uu____2411)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____2406))
in (match (uu____2399) with
| (e3, expected_c2, g'') -> begin
(

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (t_res)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____2466 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____2466))
in (

let topt1 = (tc_tactic_opt env0 topt)
in (

let f1 = (match (topt1) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(FStar_TypeChecker_Rel.map_guard f (fun f1 -> (

let uu____2475 = (FStar_Syntax_Util.mk_squash f1)
in (FStar_TypeChecker_Common.mk_by_tactic tactic uu____2475))))
end)
in (

let uu____2476 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____2476) with
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
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____2496) -> begin
(

let uu____2543 = (FStar_Syntax_Util.type_u ())
in (match (uu____2543) with
| (k, u) -> begin
(

let uu____2556 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____2556) with
| (t1, uu____2570, f) -> begin
(

let uu____2572 = (

let uu____2579 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____2579 e1))
in (match (uu____2572) with
| (e2, c, g) -> begin
(

let uu____2589 = (

let uu____2594 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____2598 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____2594 e2 c f))
in (match (uu____2589) with
| (c1, f1) -> begin
(

let uu____2607 = (

let uu____2614 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____2614 c1))
in (match (uu____2607) with
| (e3, c2, f2) -> begin
(

let uu____2654 = (

let uu____2655 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____2655))
in ((e3), (c2), (uu____2654)))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____2656; FStar_Syntax_Syntax.vars = uu____2657}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____2720 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2720) with
| (unary_op, uu____2742) -> begin
(

let head1 = (

let uu____2766 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____2766))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____2804)); FStar_Syntax_Syntax.pos = uu____2805; FStar_Syntax_Syntax.vars = uu____2806}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____2869 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2869) with
| (unary_op, uu____2891) -> begin
(

let head1 = (

let uu____2915 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____2915))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____2953; FStar_Syntax_Syntax.vars = uu____2954}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____2986 -> begin
()
end);
(

let uu____2987 = (

let uu____2994 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2994) with
| (env0, uu____3008) -> begin
(tc_term env0 e1)
end))
in (match (uu____2987) with
| (e2, c, g) -> begin
(

let uu____3022 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3022) with
| (reify_op, uu____3044) -> begin
(

let u_c = (

let uu____3066 = (tc_term env1 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____3066) with
| (uu____3073, c', uu____3075) -> begin
(

let uu____3076 = (

let uu____3077 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____3077.FStar_Syntax_Syntax.n)
in (match (uu____3076) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____3081 -> begin
(

let uu____3082 = (FStar_Syntax_Util.type_u ())
in (match (uu____3082) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3094 = (

let uu____3095 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____3096 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____3097 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____3095 uu____3096 uu____3097))))
in (failwith uu____3094))
end);
u;
))
end))
end))
end))
in (

let repr = (

let uu____3099 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_TypeChecker_Env.reify_comp env1 uu____3099 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____3120 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____3120 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____3121 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____3121) with
| (e4, c2, g') -> begin
(

let uu____3137 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e4), (c2), (uu____3137)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.pos = uu____3139; FStar_Syntax_Syntax.vars = uu____3140}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____3172 -> begin
()
end);
(

let no_reflect = (fun uu____3182 -> (

let uu____3183 = (

let uu____3184 = (

let uu____3189 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((uu____3189), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____3184))
in (FStar_Exn.raise uu____3183)))
in (

let uu____3196 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3196) with
| (reflect_op, uu____3218) -> begin
(

let uu____3239 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____3239) with
| FStar_Pervasives_Native.None -> begin
(no_reflect ())
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____3272 = (

let uu____3273 = (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____3273)))
in (match (uu____3272) with
| true -> begin
(no_reflect ())
end
| uu____3282 -> begin
(

let uu____3283 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3283) with
| (env_no_ex, topt) -> begin
(

let uu____3302 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____3322 = (

let uu____3325 = (

let uu____3326 = (

let uu____3341 = (

let uu____3344 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____3345 = (

let uu____3348 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____3348)::[])
in (uu____3344)::uu____3345))
in ((repr), (uu____3341)))
in FStar_Syntax_Syntax.Tm_app (uu____3326))
in (FStar_Syntax_Syntax.mk uu____3325))
in (uu____3322 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____3354 = (

let uu____3361 = (

let uu____3362 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____3362 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____3361 t))
in (match (uu____3354) with
| (t1, uu____3390, g) -> begin
(

let uu____3392 = (

let uu____3393 = (FStar_Syntax_Subst.compress t1)
in uu____3393.FStar_Syntax_Syntax.n)
in (match (uu____3392) with
| FStar_Syntax_Syntax.Tm_app (uu____3408, ((res, uu____3410))::((wp, uu____3412))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____3455 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____3302) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____3486 = (

let uu____3491 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____3491) with
| (e2, c, g) -> begin
((

let uu____3506 = (

let uu____3507 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____3507))
in (match (uu____3506) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 (((("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____3516 -> begin
()
end));
(

let uu____3517 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____3517) with
| FStar_Pervasives_Native.None -> begin
((

let uu____3525 = (

let uu____3532 = (

let uu____3537 = (

let uu____3538 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____3539 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____3538 uu____3539)))
in ((uu____3537), (e2.FStar_Syntax_Syntax.pos)))
in (uu____3532)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____3525));
(

let uu____3548 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e2), (uu____3548)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____3550 = (

let uu____3551 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____3551))
in ((e2), (uu____3550)))
end));
)
end))
in (match (uu____3486) with
| (e2, g) -> begin
(

let c = (

let uu____3561 = (

let uu____3562 = (

let uu____3563 = (

let uu____3564 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____3564)::[])
in (

let uu____3565 = (

let uu____3574 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3574)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____3563; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____3565; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____3562))
in (FStar_All.pipe_right uu____3561 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3594 = (comp_check_expected_typ env1 e3 c)
in (match (uu____3594) with
| (e4, c1, g') -> begin
(

let uu____3610 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e4), (c1), (uu____3610)))
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

let uu____3657 = (

let uu____3658 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____3658 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____3657 instantiate_both))
in ((

let uu____3674 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____3674) with
| true -> begin
(

let uu____3675 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3676 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____3675 uu____3676)))
end
| uu____3677 -> begin
()
end));
(

let isquote = (

let uu____3679 = (FStar_Syntax_Util.head_and_args head1)
in (match (uu____3679) with
| (head2, uu____3695) -> begin
(

let uu____3716 = (

let uu____3717 = (FStar_Syntax_Util.un_uinst head2)
in uu____3717.FStar_Syntax_Syntax.n)
in (match (uu____3716) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.quote_lid) -> begin
true
end
| uu____3721 -> begin
false
end))
end))
in (

let uu____3722 = (tc_term (no_inst env2) head1)
in (match (uu____3722) with
| (head2, chead, g_head) -> begin
(

let uu____3738 = (

let uu____3745 = ((not (env2.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____3745) with
| true -> begin
(

let uu____3752 = (

let uu____3759 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____3759))
in (match (uu____3752) with
| (e1, c, g) -> begin
(

let c1 = (

let uu____3772 = (((FStar_TypeChecker_Env.should_verify env2) && (

let uu____3774 = (FStar_Syntax_Util.is_lcomp_partial_return c)
in (not (uu____3774)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____3772) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e1 c)
end
| uu____3775 -> begin
c
end))
in ((e1), (c1), (g)))
end))
end
| uu____3776 -> begin
(

let env3 = (match (isquote) with
| true -> begin
(no_inst env2)
end
| uu____3778 -> begin
env2
end)
in (

let uu____3779 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env3 head2 chead g_head args uu____3779)))
end))
in (match (uu____3738) with
| (e1, c, g) -> begin
((

let uu____3792 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____3792) with
| true -> begin
(

let uu____3793 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____3793))
end
| uu____3794 -> begin
()
end));
(

let uu____3795 = (comp_check_expected_typ env0 e1 c)
in (match (uu____3795) with
| (e2, c1, g') -> begin
(

let gimp = (

let uu____3812 = (

let uu____3813 = (FStar_Syntax_Subst.compress head2)
in uu____3813.FStar_Syntax_Syntax.n)
in (match (uu____3812) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____3817) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e2), (c1.FStar_Syntax_Syntax.res_typ), (head2.FStar_Syntax_Syntax.pos))
in (

let uu___127_3879 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___127_3879.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___127_3879.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___127_3879.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____3928 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (

let uu____3930 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g uu____3930))
in ((

let uu____3932 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____3932) with
| true -> begin
(

let uu____3933 = (FStar_Syntax_Print.term_to_string e2)
in (

let uu____3934 = (FStar_TypeChecker_Rel.guard_to_string env2 gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____3933 uu____3934)))
end
| uu____3935 -> begin
()
end));
((e2), (c1), (gres));
)))
end));
)
end))
end)));
)))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let uu____3974 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3974) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____3994 = (tc_term env12 e1)
in (match (uu____3994) with
| (e11, c1, g1) -> begin
(

let uu____4010 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4020 = (FStar_Syntax_Util.type_u ())
in (match (uu____4020) with
| (k, uu____4030) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env1 k)
in (

let uu____4032 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in ((uu____4032), (res_t))))
end))
end)
in (match (uu____4010) with
| (env_branches, res_t) -> begin
((

let uu____4042 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____4042) with
| true -> begin
(

let uu____4043 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____4043))
end
| uu____4044 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____4129 = (

let uu____4134 = (FStar_List.fold_right (fun uu____4180 uu____4181 -> (match (((uu____4180), (uu____4181))) with
| ((uu____4244, f, c, g), (caccum, gaccum)) -> begin
(

let uu____4304 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (uu____4304)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____4134) with
| (cases, g) -> begin
(

let uu____4343 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____4343), (g)))
end))
in (match (uu____4129) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____4439 -> (match (uu____4439) with
| ((pat, wopt, br), uu____4467, lc, uu____4469) -> begin
(

let uu____4482 = (FStar_TypeChecker_Util.maybe_lift env1 br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (uu____4482)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____4537 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____4537) with
| true -> begin
(mk_match e11)
end
| uu____4540 -> begin
(

let e_match = (

let uu____4544 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____4544))
in (

let lb = (

let uu____4548 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = uu____4548; FStar_Syntax_Syntax.lbdef = e11})
in (

let e2 = (

let uu____4552 = (

let uu____4555 = (

let uu____4556 = (

let uu____4569 = (

let uu____4570 = (

let uu____4571 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____4571)::[])
in (FStar_Syntax_Subst.close uu____4570 e_match))
in ((((false), ((lb)::[]))), (uu____4569)))
in FStar_Syntax_Syntax.Tm_let (uu____4556))
in (FStar_Syntax_Syntax.mk uu____4555))
in (uu____4552 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____4584 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____4584) with
| true -> begin
(

let uu____4585 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____4586 = (

let uu____4587 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____4587))
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____4585 uu____4586)))
end
| uu____4588 -> begin
()
end));
(

let uu____4589 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e2), (cres), (uu____4589)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4592); FStar_Syntax_Syntax.lbunivs = uu____4593; FStar_Syntax_Syntax.lbtyp = uu____4594; FStar_Syntax_Syntax.lbeff = uu____4595; FStar_Syntax_Syntax.lbdef = uu____4596})::[]), uu____4597) -> begin
((

let uu____4617 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____4617) with
| true -> begin
(

let uu____4618 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____4618))
end
| uu____4619 -> begin
()
end));
(check_top_level_let env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____4620), uu____4621) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4636); FStar_Syntax_Syntax.lbunivs = uu____4637; FStar_Syntax_Syntax.lbtyp = uu____4638; FStar_Syntax_Syntax.lbeff = uu____4639; FStar_Syntax_Syntax.lbdef = uu____4640})::uu____4641), uu____4642) -> begin
((

let uu____4664 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____4664) with
| true -> begin
(

let uu____4665 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____4665))
end
| uu____4666 -> begin
()
end));
(check_top_level_let_rec env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____4667), uu____4668) -> begin
(check_inner_let_rec env1 top)
end));
)))
and tc_synth : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env args rng -> (

let uu____4694 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.None), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4784))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.Some (a)), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4844))))::((uu____4845, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4846))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.Some (a)), (rest))
end
| uu____4919 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("synth_by_tactic: bad application"), (rng)))))
end)
in (match (uu____4694) with
| (tau, atyp, rest) -> begin
(

let typ = (match (atyp) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5003 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____5003) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5009 = (

let uu____5010 = (

let uu____5015 = (FStar_TypeChecker_Env.get_range env)
in (("synth_by_tactic: need a type annotation when no expected type is present"), (uu____5015)))
in FStar_Errors.Error (uu____5010))
in (FStar_Exn.raise uu____5009))
end))
end)
in (

let uu____5018 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____5018) with
| (env', uu____5032) -> begin
(

let uu____5037 = (tc_term env' typ)
in (match (uu____5037) with
| (typ1, uu____5051, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g1);
(

let uu____5054 = (tc_tactic env' tau)
in (match (uu____5054) with
| (tau1, uu____5068, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g2);
(

let t = (match (env.FStar_TypeChecker_Env.nosynth) with
| true -> begin
(

let uu____5076 = (

let uu____5077 = (FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.magic_lid)
in (

let uu____5078 = (

let uu____5079 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____5079)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____5077 uu____5078)))
in (uu____5076 FStar_Pervasives_Native.None rng))
end
| uu____5082 -> begin
(

let t = (env.FStar_TypeChecker_Env.synth env' typ1 tau1)
in ((

let uu____5085 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____5085) with
| true -> begin
(

let uu____5086 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____5086))
end
| uu____5087 -> begin
()
end));
t;
))
end)
in ((FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(

let uu____5089 = (FStar_Syntax_Syntax.mk_Tm_app t rest FStar_Pervasives_Native.None rng)
in (tc_term env uu____5089));
));
)
end));
)
end))
end)))
end)))
and tc_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___128_5093 = env
in {FStar_TypeChecker_Env.solver = uu___128_5093.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___128_5093.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___128_5093.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___128_5093.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___128_5093.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___128_5093.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___128_5093.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___128_5093.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___128_5093.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___128_5093.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___128_5093.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___128_5093.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___128_5093.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___128_5093.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___128_5093.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___128_5093.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___128_5093.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___128_5093.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___128_5093.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___128_5093.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___128_5093.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___128_5093.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___128_5093.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___128_5093.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___128_5093.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___128_5093.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___128_5093.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___128_5093.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___128_5093.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___128_5093.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___128_5093.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___128_5093.FStar_TypeChecker_Env.dsenv})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit)))
and tc_reified_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___129_5097 = env
in {FStar_TypeChecker_Env.solver = uu___129_5097.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___129_5097.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___129_5097.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___129_5097.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___129_5097.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___129_5097.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___129_5097.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___129_5097.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___129_5097.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___129_5097.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___129_5097.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___129_5097.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___129_5097.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___129_5097.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___129_5097.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___129_5097.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___129_5097.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___129_5097.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___129_5097.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___129_5097.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___129_5097.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___129_5097.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___129_5097.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___129_5097.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___129_5097.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___129_5097.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___129_5097.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___129_5097.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___129_5097.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___129_5097.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___129_5097.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___129_5097.FStar_TypeChecker_Env.dsenv})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____5113 = (tc_tactic env tactic)
in (match (uu____5113) with
| (tactic1, uu____5123, uu____5124) -> begin
FStar_Pervasives_Native.Some (tactic1)
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t -> (

let uu____5163 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____5163) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____5184 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5184) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____5189 -> begin
(

let uu____5190 = (

let uu____5191 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5191))
in FStar_Util.Inr (uu____5190))
end))
in (

let is_data_ctor = (fun uu___116_5201 -> (match (uu___116_5201) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5204)) -> begin
true
end
| uu____5211 -> begin
false
end))
in (

let uu____5214 = ((is_data_ctor dc) && (

let uu____5216 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____5216))))
in (match (uu____5214) with
| true -> begin
(

let uu____5223 = (

let uu____5224 = (

let uu____5229 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____5230 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____5229), (uu____5230))))
in FStar_Errors.Error (uu____5224))
in (FStar_Exn.raise uu____5223))
end
| uu____5237 -> begin
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

let uu____5247 = (

let uu____5248 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____5248))
in (failwith uu____5247))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____5282 = (

let uu____5283 = (FStar_Syntax_Subst.compress t1)
in uu____5283.FStar_Syntax_Syntax.n)
in (match (uu____5282) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5286) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____5299 -> begin
(

let imp = (("uvar in term"), (env1), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___130_5337 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___130_5337.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___130_5337.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___130_5337.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env1 e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____5389 = (

let uu____5402 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____5402) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5417 = (FStar_Syntax_Util.type_u ())
in (match (uu____5417) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____5389) with
| (t, uu____5454, g0) -> begin
(

let uu____5468 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____5468) with
| (e1, uu____5488, g1) -> begin
(

let uu____5502 = (

let uu____5503 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____5503 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____5504 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e1), (uu____5502), (uu____5504))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____5506 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____5519 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____5519)))
end
| uu____5522 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____5506) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___131_5538 = x
in {FStar_Syntax_Syntax.ppname = uu___131_5538.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_5538.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Env.insert_bv_info env1 x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____5541 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____5541) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____5562 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5562) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____5567 -> begin
(

let uu____5568 = (

let uu____5569 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5569))
in FStar_Util.Inr (uu____5568))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5575; FStar_Syntax_Syntax.vars = uu____5576}, uu____5577) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____5582 = (

let uu____5583 = (

let uu____5588 = (FStar_TypeChecker_Env.get_range env1)
in (("Badly instantiated synth_by_tactic"), (uu____5588)))
in FStar_Errors.Error (uu____5583))
in (FStar_Exn.raise uu____5582))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____5596 = (

let uu____5597 = (

let uu____5602 = (FStar_TypeChecker_Env.get_range env1)
in (("Badly instantiated synth_by_tactic"), (uu____5602)))
in FStar_Errors.Error (uu____5597))
in (FStar_Exn.raise uu____5596))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5610; FStar_Syntax_Syntax.vars = uu____5611}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____5620 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5620) with
| ((us', t), range) -> begin
((match ((Prims.op_disEquality (FStar_List.length us1) (FStar_List.length us'))) with
| true -> begin
(

let uu____5643 = (

let uu____5644 = (

let uu____5649 = (

let uu____5650 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____5651 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____5652 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____5650 uu____5651 uu____5652))))
in (

let uu____5653 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____5649), (uu____5653))))
in FStar_Errors.Error (uu____5644))
in (FStar_Exn.raise uu____5643))
end
| uu____5654 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____5669 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____5673 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5673 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5675 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5675) with
| ((us, t), range) -> begin
((

let uu____5698 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____5698) with
| true -> begin
(

let uu____5699 = (

let uu____5700 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____5700))
in (

let uu____5701 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____5702 = (FStar_Range.string_of_range range)
in (

let uu____5703 = (FStar_Range.string_of_use_range range)
in (

let uu____5704 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____5699 uu____5701 uu____5702 uu____5703 uu____5704))))))
end
| uu____5705 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____5709 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5709 us))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (

let e1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 e1 (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____5733 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____5733) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____5747 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5747) with
| (env2, uu____5761) -> begin
(

let uu____5766 = (tc_binders env2 bs1)
in (match (uu____5766) with
| (bs2, env3, g, us) -> begin
(

let uu____5785 = (tc_comp env3 c1)
in (match (uu____5785) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___132_5804 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___132_5804.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___132_5804.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____5813 = (FStar_TypeChecker_Rel.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Rel.conj_guard g uu____5813))
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

let uu____5832 = (

let uu____5837 = (

let uu____5838 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5838)::[])
in (FStar_Syntax_Subst.open_term uu____5837 phi))
in (match (uu____5832) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____5848 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5848) with
| (env2, uu____5862) -> begin
(

let uu____5867 = (

let uu____5880 = (FStar_List.hd x1)
in (tc_binder env2 uu____5880))
in (match (uu____5867) with
| (x2, env3, f1, u) -> begin
((

let uu____5908 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____5908) with
| true -> begin
(

let uu____5909 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____5910 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____5911 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____5909 uu____5910 uu____5911))))
end
| uu____5912 -> begin
()
end));
(

let uu____5913 = (FStar_Syntax_Util.type_u ())
in (match (uu____5913) with
| (t_phi, uu____5925) -> begin
(

let uu____5926 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____5926) with
| (phi2, uu____5940, f2) -> begin
(

let e1 = (

let uu___133_5945 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___133_5945.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___133_5945.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____5952 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____5952))
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____5965) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____5988 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____5988) with
| true -> begin
(

let uu____5989 = (FStar_Syntax_Print.term_to_string (

let uu___134_5992 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.pos = uu___134_5992.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___134_5992.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____5989))
end
| uu____5997 -> begin
()
end));
(

let uu____5998 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____5998) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____6011 -> begin
(

let uu____6012 = (

let uu____6013 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____6014 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____6013 uu____6014)))
in (failwith uu____6012))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Syntax_Syntax.t_unit
end
| FStar_Const.Const_bool (uu____6023) -> begin
FStar_Syntax_Util.t_bool
end
| FStar_Const.Const_int (uu____6024, FStar_Pervasives_Native.None) -> begin
FStar_Syntax_Syntax.t_int
end
| FStar_Const.Const_int (uu____6035, FStar_Pervasives_Native.Some (uu____6036)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____6051) -> begin
FStar_Syntax_Syntax.t_string
end
| FStar_Const.Const_float (uu____6056) -> begin
FStar_Syntax_Syntax.t_float
end
| FStar_Const.Const_char (uu____6057) -> begin
FStar_Syntax_Syntax.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____6058) -> begin
FStar_Syntax_Syntax.t_range
end
| uu____6059 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____6076) -> begin
(

let uu____6085 = (FStar_Syntax_Util.type_u ())
in (match (uu____6085) with
| (k, u) -> begin
(

let uu____6098 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____6098) with
| (t1, uu____6112, g) -> begin
(

let uu____6114 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____6114), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____6116) -> begin
(

let uu____6125 = (FStar_Syntax_Util.type_u ())
in (match (uu____6125) with
| (k, u) -> begin
(

let uu____6138 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____6138) with
| (t1, uu____6152, g) -> begin
(

let uu____6154 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____6154), (u), (g)))
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

let uu____6162 = (

let uu____6163 = (

let uu____6164 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____6164)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____6163))
in (uu____6162 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____6167 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____6167) with
| (tc1, uu____6181, f) -> begin
(

let uu____6183 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____6183) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____6227 = (

let uu____6228 = (FStar_Syntax_Subst.compress head3)
in uu____6228.FStar_Syntax_Syntax.n)
in (match (uu____6227) with
| FStar_Syntax_Syntax.Tm_uinst (uu____6231, us) -> begin
us
end
| uu____6237 -> begin
[]
end))
in (

let uu____6238 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____6238) with
| (uu____6259, args1) -> begin
(

let uu____6281 = (

let uu____6300 = (FStar_List.hd args1)
in (

let uu____6313 = (FStar_List.tl args1)
in ((uu____6300), (uu____6313))))
in (match (uu____6281) with
| (res, args2) -> begin
(

let uu____6378 = (

let uu____6387 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___117_6415 -> (match (uu___117_6415) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____6423 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____6423) with
| (env1, uu____6435) -> begin
(

let uu____6440 = (tc_tot_or_gtot_term env1 e)
in (match (uu____6440) with
| (e1, uu____6452, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____6387 FStar_List.unzip))
in (match (uu____6378) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___135_6491 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___135_6491.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___135_6491.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____6495 = (FStar_TypeChecker_Env.effect_repr env c2 u)
in (match (uu____6495) with
| FStar_Pervasives_Native.None -> begin
u
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____6499 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c2), (u_c), (uu____6499))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____6507) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____6508) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____6518 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____6518))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____6522 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____6522))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u2
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____6526 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____6527 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6527 FStar_Pervasives_Native.snd))
end
| uu____6536 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (

let uu____6560 = (

let uu____6561 = (

let uu____6566 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((uu____6566), (top.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____6561))
in (FStar_Exn.raise uu____6560)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____6656 bs2 bs_expected1 -> (match (uu____6656) with
| (env2, out, g, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.None), (g), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((match (((imp), (imp'))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6824))) -> begin
(

let uu____6829 = (

let uu____6830 = (

let uu____6835 = (

let uu____6836 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____6836))
in (

let uu____6837 = (FStar_Syntax_Syntax.range_of_bv hd1)
in ((uu____6835), (uu____6837))))
in FStar_Errors.Error (uu____6830))
in (FStar_Exn.raise uu____6829))
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6838)), FStar_Pervasives_Native.None) -> begin
(

let uu____6843 = (

let uu____6844 = (

let uu____6849 = (

let uu____6850 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____6850))
in (

let uu____6851 = (FStar_Syntax_Syntax.range_of_bv hd1)
in ((uu____6849), (uu____6851))))
in FStar_Errors.Error (uu____6844))
in (FStar_Exn.raise uu____6843))
end
| uu____6852 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____6858 = (

let uu____6863 = (

let uu____6864 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____6864.FStar_Syntax_Syntax.n)
in (match (uu____6863) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____6871 -> begin
((

let uu____6873 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____6873) with
| true -> begin
(

let uu____6874 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____6874))
end
| uu____6875 -> begin
()
end));
(

let uu____6876 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____6876) with
| (t, uu____6888, g1) -> begin
(

let g2 = (

let uu____6891 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____6892 = (FStar_TypeChecker_Rel.teq env2 t expected_t)
in (FStar_TypeChecker_Util.label_guard uu____6891 "Type annotation on parameter incompatible with the expected type" uu____6892)))
in (

let g3 = (

let uu____6894 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____6894))
in ((t), (g3))))
end));
)
end))
in (match (uu____6858) with
| (t, g1) -> begin
(

let hd2 = (

let uu___136_6922 = hd1
in {FStar_Syntax_Syntax.ppname = uu___136_6922.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_6922.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env3 = (push_binding env2 b)
in (

let subst2 = (

let uu____6935 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____6935))
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
| uu____7081 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____7088 = (tc_binders env1 bs)
in (match (uu____7088) with
| (bs1, envbody, g, uu____7118) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody), (body1), (g))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____7162 = (

let uu____7163 = (FStar_Syntax_Subst.compress t2)
in uu____7163.FStar_Syntax_Syntax.n)
in (match (uu____7162) with
| FStar_Syntax_Syntax.Tm_uvar (uu____7186) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____7208 -> begin
(failwith "Impossible")
end);
(

let uu____7215 = (tc_binders env1 bs)
in (match (uu____7215) with
| (bs1, envbody, g, uu____7247) -> begin
(

let uu____7248 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____7248) with
| (envbody1, uu____7276) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____7287); FStar_Syntax_Syntax.pos = uu____7288; FStar_Syntax_Syntax.vars = uu____7289}, uu____7290) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____7332 -> begin
(failwith "Impossible")
end);
(

let uu____7339 = (tc_binders env1 bs)
in (match (uu____7339) with
| (bs1, envbody, g, uu____7371) -> begin
(

let uu____7372 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____7372) with
| (envbody1, uu____7400) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____7412) -> begin
(

let uu____7417 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____7417) with
| (uu____7458, bs1, bs', copt, env2, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), (bs'), (copt), (env2), (body2), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____7501 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____7501) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 -> (

let rec handle_more = (fun uu____7601 c_expected2 -> (match (uu____7601) with
| (env3, bs2, more, guard, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7716 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env3), (bs2), (guard), (uu____7716)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____7747 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____7747))
in (

let uu____7748 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env3), (bs2), (guard), (uu____7748))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (

let uu____7773 = ((FStar_Options.ml_ish ()) || (FStar_Syntax_Util.is_named_tot c))
in (match (uu____7773) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env3 (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____7821 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____7821) with
| (bs_expected4, c_expected4) -> begin
(

let uu____7842 = (check_binders env3 more_bs bs_expected4)
in (match (uu____7842) with
| (env4, bs', more1, guard', subst2) -> begin
(

let uu____7890 = (

let uu____7921 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env4), ((FStar_List.append bs2 bs')), (more1), (uu____7921), (subst2)))
in (handle_more uu____7890 c_expected4))
end))
end))
end
| uu____7938 -> begin
(

let uu____7939 = (

let uu____7940 = (FStar_Syntax_Print.term_to_string t3)
in (FStar_Util.format1 "More arguments than annotated type (%s)" uu____7940))
in (fail uu____7939 t3))
end))
end
| uu____7955 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t2)
end)))
end)
end))
in (

let uu____7970 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____7970 c_expected1))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___137_8029 = envbody
in {FStar_TypeChecker_Env.solver = uu___137_8029.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___137_8029.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___137_8029.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___137_8029.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___137_8029.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___137_8029.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___137_8029.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___137_8029.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___137_8029.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___137_8029.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___137_8029.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___137_8029.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___137_8029.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___137_8029.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___137_8029.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___137_8029.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___137_8029.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___137_8029.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___137_8029.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___137_8029.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___137_8029.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___137_8029.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___137_8029.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___137_8029.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___137_8029.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___137_8029.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___137_8029.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___137_8029.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___137_8029.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___137_8029.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___137_8029.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___137_8029.FStar_TypeChecker_Env.dsenv})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____8068 uu____8069 -> (match (((uu____8068), (uu____8069))) with
| ((env2, letrec_binders), (l, t3)) -> begin
(

let uu____8114 = (

let uu____8121 = (

let uu____8122 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____8122 FStar_Pervasives_Native.fst))
in (tc_term uu____8121 t3))
in (match (uu____8114) with
| (t4, uu____8144, uu____8145) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l (([]), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____8155 = (FStar_Syntax_Syntax.mk_binder (

let uu___138_8158 = x
in {FStar_Syntax_Syntax.ppname = uu___138_8158.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_8158.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____8155)::letrec_binders)
end
| uu____8159 -> begin
letrec_binders
end)
in ((env3), (lb))))
end))
end)) ((envbody1), ([])))))))
in (

let uu____8164 = (check_actuals_against_formals env1 bs bs_expected1)
in (match (uu____8164) with
| (envbody, bs1, g, c) -> begin
(

let uu____8215 = (

let uu____8222 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____8222) with
| true -> begin
(mk_letrec_env envbody bs1 c)
end
| uu____8229 -> begin
((envbody), ([]))
end))
in (match (uu____8215) with
| (envbody1, letrecs) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in ((FStar_Pervasives_Native.Some (t2)), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (envbody2), (body1), (g)))
end))
end))))
end))
end
| uu____8271 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____8292 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____8292))
end
| uu____8293 -> begin
(

let uu____8294 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____8294) with
| (uu____8333, bs1, uu____8335, c_opt, envbody, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (c_opt), (envbody), (body2), (g))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____8355 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8355) with
| (env1, topt) -> begin
((

let uu____8375 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____8375) with
| true -> begin
(

let uu____8376 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____8376 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____8378 -> begin
"false"
end)))
end
| uu____8379 -> begin
()
end));
(

let uu____8380 = (expected_function_typ1 env1 topt body)
in (match (uu____8380) with
| (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1, g) -> begin
(

let uu____8420 = (

let should_check_expected_effect = (

let uu____8428 = (

let uu____8435 = (

let uu____8436 = (FStar_Syntax_Subst.compress body1)
in uu____8436.FStar_Syntax_Syntax.n)
in ((c_opt), (uu____8435)))
in (match (uu____8428) with
| (FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Tm_ascribed (uu____8441, (FStar_Util.Inr (expected_c), uu____8443), uu____8444)) -> begin
false
end
| uu____8493 -> begin
true
end))
in (

let uu____8500 = (tc_term (

let uu___139_8509 = envbody
in {FStar_TypeChecker_Env.solver = uu___139_8509.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___139_8509.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___139_8509.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___139_8509.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___139_8509.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___139_8509.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___139_8509.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___139_8509.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___139_8509.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___139_8509.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___139_8509.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___139_8509.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___139_8509.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___139_8509.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___139_8509.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___139_8509.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___139_8509.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___139_8509.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___139_8509.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___139_8509.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___139_8509.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___139_8509.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___139_8509.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___139_8509.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___139_8509.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___139_8509.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___139_8509.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___139_8509.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___139_8509.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___139_8509.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___139_8509.FStar_TypeChecker_Env.dsenv}) body1)
in (match (uu____8500) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (match (should_check_expected_effect) with
| true -> begin
(

let uu____8526 = (

let uu____8533 = (

let uu____8538 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body2), (uu____8538)))
in (check_expected_effect (

let uu___140_8545 = envbody
in {FStar_TypeChecker_Env.solver = uu___140_8545.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___140_8545.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___140_8545.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___140_8545.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___140_8545.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___140_8545.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___140_8545.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___140_8545.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___140_8545.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___140_8545.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___140_8545.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___140_8545.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___140_8545.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___140_8545.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___140_8545.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___140_8545.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___140_8545.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___140_8545.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___140_8545.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___140_8545.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___140_8545.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___140_8545.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___140_8545.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___140_8545.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___140_8545.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___140_8545.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___140_8545.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___140_8545.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___140_8545.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___140_8545.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___140_8545.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___140_8545.FStar_TypeChecker_Env.dsenv}) c_opt uu____8533))
in (match (uu____8526) with
| (body3, cbody1, guard) -> begin
(

let uu____8555 = (FStar_TypeChecker_Rel.conj_guard guard_body1 guard)
in ((body3), (cbody1), (uu____8555)))
end))
end
| uu____8556 -> begin
(

let uu____8557 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body2), (uu____8557), (guard_body1)))
end))
end)))
in (match (uu____8420) with
| (body2, cbody, guard) -> begin
(

let guard1 = (

let uu____8572 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____8574 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____8574))))
in (match (uu____8572) with
| true -> begin
(

let uu____8575 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____8575))
end
| uu____8576 -> begin
(

let guard1 = (

let uu____8578 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard env1 (FStar_List.append bs1 letrec_binders) uu____8578))
in guard1)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody)
in (

let e = (FStar_Syntax_Util.abs bs1 body2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody c_opt)))))
in (

let uu____8587 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____8608) -> begin
((e), (t1), (guard1))
end
| uu____8621 -> begin
(

let uu____8622 = (FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
in (match (uu____8622) with
| (e1, guard') -> begin
(

let uu____8635 = (FStar_TypeChecker_Rel.conj_guard guard1 guard')
in ((e1), (t1), (uu____8635)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard1))
end)
in (match (uu____8587) with
| (e1, tfun, guard2) -> begin
(

let c = (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____8648 -> begin
(FStar_TypeChecker_Util.return_value env1 tfun e1)
end)
in (

let uu____8649 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 (FStar_Syntax_Util.lcomp_of_comp c) guard2)
in (match (uu____8649) with
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

let uu____8698 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8698) with
| true -> begin
(

let uu____8699 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____8700 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____8699 uu____8700)))
end
| uu____8701 -> begin
()
end));
(

let monadic_application = (fun uu____8757 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____8757) with
| (head2, chead1, ghead1, cres) -> begin
(

let rt = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres1 = (

let uu___141_8816 = cres
in {FStar_Syntax_Syntax.eff_name = uu___141_8816.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___141_8816.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___141_8816.FStar_Syntax_Syntax.comp})
in (

let uu____8817 = (match (bs) with
| [] -> begin
(

let cres2 = (FStar_TypeChecker_Util.subst_lcomp subst1 cres1)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in ((cres2), (g))))
end
| uu____8832 -> begin
(

let g = (

let uu____8840 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____8840 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (

let uu____8841 = (

let uu____8842 = (

let uu____8845 = (

let uu____8846 = (

let uu____8847 = (cres1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs uu____8847))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst1) uu____8846))
in (FStar_Syntax_Syntax.mk_Total uu____8845))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8842))
in ((uu____8841), (g))))
end)
in (match (uu____8817) with
| (cres2, guard1) -> begin
((

let uu____8861 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____8861) with
| true -> begin
(

let uu____8862 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____8862))
end
| uu____8863 -> begin
()
end));
(

let cres3 = (

let uu____8865 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2)
in (match (uu____8865) with
| true -> begin
(

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2))
end
| uu____8875 -> begin
cres2
end))
in (

let comp = (FStar_List.fold_left (fun out_c uu____8899 -> (match (uu____8899) with
| ((e, q), x, c) -> begin
(

let uu____8932 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____8932) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____8937 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end))
end)) cres3 arg_comps_rev)
in (

let comp1 = (FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
in (

let shortcuts_evaluation_order = (

let uu____8944 = (

let uu____8945 = (FStar_Syntax_Subst.compress head2)
in uu____8945.FStar_Syntax_Syntax.n)
in (match (uu____8944) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____8949 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____8970 -> (match (uu____8970) with
| (arg, uu____8984, uu____8985) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ))))
end
| uu____8994 -> begin
(

let uu____8995 = (

let map_fun = (fun uu____9057 -> (match (uu____9057) with
| ((e, q), uu____9092, c) -> begin
(

let uu____9102 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____9102) with
| true -> begin
((FStar_Pervasives_Native.None), (((e), (q))))
end
| uu____9149 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____9152 = (

let uu____9157 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____9157), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____9152)))))
end))
end))
in (

let uu____9186 = (

let uu____9211 = (

let uu____9234 = (

let uu____9249 = (

let uu____9258 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____9258), (FStar_Pervasives_Native.None), (chead1)))
in (uu____9249)::arg_comps_rev)
in (FStar_List.map map_fun uu____9234))
in (FStar_All.pipe_left FStar_List.split uu____9211))
in (match (uu____9186) with
| (lifted_args, reverse_args) -> begin
(

let uu____9431 = (

let uu____9432 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____9432))
in (

let uu____9441 = (

let uu____9448 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____9448))
in ((lifted_args), (uu____9431), (uu____9441))))
end)))
in (match (uu____8995) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___118_9551 -> (match (uu___118_9551) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1)
in (

let letbinding = (

let uu____9606 = (

let uu____9609 = (

let uu____9610 = (

let uu____9623 = (

let uu____9624 = (

let uu____9625 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____9625)::[])
in (FStar_Syntax_Subst.close uu____9624 e))
in ((((false), ((lb)::[]))), (uu____9623)))
in FStar_Syntax_Syntax.Tm_let (uu____9610))
in (FStar_Syntax_Syntax.mk uu____9609))
in (uu____9606 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp1.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____9655 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp1 guard1)
in (match (uu____9655) with
| (comp2, g) -> begin
((app), (comp2), (g))
end)))))));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____9746 bs args1 -> (match (uu____9746) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9893))))::rest, ((uu____9895, FStar_Pervasives_Native.None))::uu____9896) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let t1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (

let uu____9957 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____9957) with
| (varg, uu____9977, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____9999 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____9999)))
in (

let uu____10000 = (

let uu____10035 = (

let uu____10050 = (

let uu____10063 = (

let uu____10064 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____10064 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____10063)))
in (uu____10050)::outargs)
in (

let uu____10083 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst2), (uu____10035), ((arg)::arg_rets), (uu____10083), (fvs))))
in (tc_args head_info uu____10000 rest args1))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10185)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10186))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____10199 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___142_10210 = x
in {FStar_Syntax_Syntax.ppname = uu___142_10210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_10210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____10212 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10212) with
| true -> begin
(

let uu____10213 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____10213))
end
| uu____10214 -> begin
()
end));
(

let targ1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___143_10218 = env1
in {FStar_TypeChecker_Env.solver = uu___143_10218.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___143_10218.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___143_10218.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___143_10218.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___143_10218.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___143_10218.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___143_10218.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___143_10218.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___143_10218.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___143_10218.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___143_10218.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___143_10218.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___143_10218.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___143_10218.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___143_10218.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___143_10218.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___143_10218.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___143_10218.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___143_10218.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___143_10218.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___143_10218.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___143_10218.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___143_10218.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___143_10218.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___143_10218.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___143_10218.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___143_10218.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___143_10218.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___143_10218.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___143_10218.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___143_10218.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___143_10218.FStar_TypeChecker_Env.dsenv})
in ((

let uu____10220 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____10220) with
| true -> begin
(

let uu____10221 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____10222 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____10223 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____10221 uu____10222 uu____10223))))
end
| uu____10224 -> begin
()
end));
(

let uu____10225 = (tc_term env2 e)
in (match (uu____10225) with
| (e1, c, g_e) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____10252 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____10252))
in (

let uu____10253 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____10253) with
| true -> begin
(

let subst2 = (

let uu____10261 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____10261 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____10310 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
))));
)));
)
end
| (uu____10355, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____10391) -> begin
(

let uu____10442 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____10442) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 tres -> (

let tres1 = (

let uu____10476 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____10476 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____10501 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____10501) with
| (bs2, cres'1) -> begin
(

let head_info1 = ((head2), (chead1), (ghead1), ((FStar_Syntax_Util.lcomp_of_comp cres'1)))
in ((

let uu____10524 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____10524) with
| true -> begin
(FStar_Errors.warn tres1.FStar_Syntax_Syntax.pos "Potentially redundant explicit currying of a function type")
end
| uu____10525 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____10566 when (not (norm1)) -> begin
(

let uu____10567 = (FStar_TypeChecker_Normalize.unfold_whnf env tres1)
in (aux true uu____10567))
end
| uu____10568 -> begin
(

let uu____10569 = (

let uu____10570 = (

let uu____10575 = (

let uu____10576 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____10577 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" uu____10576 uu____10577)))
in (

let uu____10584 = (FStar_Syntax_Syntax.argpos arg)
in ((uu____10575), (uu____10584))))
in FStar_Errors.Error (uu____10570))
in (FStar_Exn.raise uu____10569))
end)))
in (aux false chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf -> (

let uu____10603 = (

let uu____10604 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____10604.FStar_Syntax_Syntax.n)
in (match (uu____10603) with
| FStar_Syntax_Syntax.Tm_uvar (uu____10615) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____10716 = (tc_term env1 e)
in (match (uu____10716) with
| (e1, c, g_e) -> begin
(

let uu____10738 = (tc_args1 env1 tl1)
in (match (uu____10738) with
| (args2, comps, g_rest) -> begin
(

let uu____10778 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____10778)))
end))
end))
end))
in (

let uu____10799 = (tc_args1 env args)
in (match (uu____10799) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____10836 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____10874 -> (match (uu____10874) with
| (uu____10887, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____10836))
in (

let ml_or_tot = (fun t r1 -> (

let uu____10904 = (FStar_Options.ml_ish ())
in (match (uu____10904) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____10905 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____10907 = (

let uu____10910 = (

let uu____10911 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____10911 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____10910))
in (ml_or_tot uu____10907 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____10924 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____10924) with
| true -> begin
(

let uu____10925 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____10926 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____10927 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____10925 uu____10926 uu____10927))))
end
| uu____10928 -> begin
()
end));
(

let uu____10930 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____10930));
(

let comp = (

let uu____10932 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____10943 out -> (match (uu____10943) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____10932))
in (

let uu____10957 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let uu____10960 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____10957), (comp), (uu____10960)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____10963); FStar_Syntax_Syntax.pos = uu____10964; FStar_Syntax_Syntax.vars = uu____10965}, uu____10966) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____11087 = (tc_term env1 e)
in (match (uu____11087) with
| (e1, c, g_e) -> begin
(

let uu____11109 = (tc_args1 env1 tl1)
in (match (uu____11109) with
| (args2, comps, g_rest) -> begin
(

let uu____11149 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____11149)))
end))
end))
end))
in (

let uu____11170 = (tc_args1 env args)
in (match (uu____11170) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____11207 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____11245 -> (match (uu____11245) with
| (uu____11258, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____11207))
in (

let ml_or_tot = (fun t r1 -> (

let uu____11275 = (FStar_Options.ml_ish ())
in (match (uu____11275) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____11276 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____11278 = (

let uu____11281 = (

let uu____11282 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____11282 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____11281))
in (ml_or_tot uu____11278 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____11295 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____11295) with
| true -> begin
(

let uu____11296 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____11297 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____11298 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____11296 uu____11297 uu____11298))))
end
| uu____11299 -> begin
()
end));
(

let uu____11301 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____11301));
(

let comp = (

let uu____11303 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____11314 out -> (match (uu____11314) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____11303))
in (

let uu____11328 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let uu____11331 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____11328), (comp), (uu____11331)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____11352 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____11352) with
| (bs1, c1) -> begin
(

let head_info = ((head1), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c1)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs1 args))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____11417) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____11423, uu____11424) -> begin
(check_function_app t)
end
| uu____11465 -> begin
(

let uu____11466 = (

let uu____11467 = (

let uu____11472 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((uu____11472), (head1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____11467))
in (FStar_Exn.raise uu____11466))
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

let uu____11542 = (FStar_List.fold_left2 (fun uu____11585 uu____11586 uu____11587 -> (match (((uu____11585), (uu____11586), (uu____11587))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((Prims.op_disEquality aq aq')) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____11654 -> begin
()
end);
(

let uu____11655 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____11655) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____11673 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____11673 g))
in (

let ghost1 = (ghost || ((

let uu____11677 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____11677))) && (

let uu____11679 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____11679)))))
in (

let uu____11680 = (

let uu____11689 = (

let uu____11698 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____11698)::[])
in (FStar_List.append seen uu____11689))
in (

let uu____11705 = (FStar_TypeChecker_Rel.conj_guard guard g1)
in ((uu____11680), (uu____11705), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____11542) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____11741 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____11741 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____11742 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____11743 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____11743) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____11760 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____11794 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____11794) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____11830 = branch1
in (match (uu____11830) with
| (cpat, uu____11862, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let tc_annot = (fun env1 t -> (

let uu____11921 = (FStar_Syntax_Util.type_u ())
in (match (uu____11921) with
| (tu, u) -> begin
(

let uu____11928 = (tc_check_tot_or_gtot_term env1 t tu)
in (match (uu____11928) with
| (t1, uu____11936, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
t1;
)
end))
end)))
in (

let uu____11939 = (FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 tc_annot)
in (match (uu____11939) with
| (pat_bvs1, exp, p) -> begin
((

let uu____11968 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____11968) with
| true -> begin
(

let uu____11969 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____11970 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____11969 uu____11970)))
end
| uu____11971 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs1)
in (

let uu____11973 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____11973) with
| (env1, uu____11993) -> begin
(

let env11 = (

let uu___144_11999 = env1
in {FStar_TypeChecker_Env.solver = uu___144_11999.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___144_11999.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___144_11999.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___144_11999.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___144_11999.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___144_11999.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___144_11999.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___144_11999.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___144_11999.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___144_11999.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___144_11999.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___144_11999.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___144_11999.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___144_11999.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___144_11999.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___144_11999.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___144_11999.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___144_11999.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___144_11999.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___144_11999.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___144_11999.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___144_11999.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___144_11999.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___144_11999.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___144_11999.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___144_11999.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___144_11999.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___144_11999.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___144_11999.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___144_11999.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___144_11999.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___144_11999.FStar_TypeChecker_Env.dsenv})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in ((

let uu____12002 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____12002) with
| true -> begin
(

let uu____12003 = (FStar_Syntax_Print.term_to_string exp)
in (

let uu____12004 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____12003 uu____12004)))
end
| uu____12005 -> begin
()
end));
(

let env12 = (FStar_TypeChecker_Env.set_expected_typ env11 expected_pat_t)
in (

let uu____12007 = (tc_tot_or_gtot_term env12 exp)
in (match (uu____12007) with
| (exp1, lc, g) -> begin
(

let g1 = (

let uu___145_12030 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___145_12030.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___145_12030.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___145_12030.FStar_TypeChecker_Env.implicits})
in (

let uu____12031 = (

let g' = (FStar_TypeChecker_Rel.teq env12 lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g2 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in (

let env13 = (FStar_TypeChecker_Env.set_range env12 exp1.FStar_Syntax_Syntax.pos)
in (

let uu____12035 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env13 g2)
in (FStar_All.pipe_right uu____12035 FStar_TypeChecker_Rel.resolve_implicits)))))
in (

let norm_exp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env12 exp1)
in (

let uvs1 = (FStar_Syntax_Free.uvars norm_exp)
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____12052 = (

let uu____12053 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____12053))
in (match (uu____12052) with
| true -> begin
(

let unresolved = (

let uu____12065 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right uu____12065 FStar_Util.set_elements))
in (

let uu____12092 = (

let uu____12093 = (

let uu____12098 = (

let uu____12099 = (FStar_TypeChecker_Normalize.term_to_string env norm_exp)
in (

let uu____12100 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____12101 = (

let uu____12102 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____12120 -> (match (uu____12120) with
| (u, uu____12126) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____12102 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____12099 uu____12100 uu____12101))))
in ((uu____12098), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____12093))
in (FStar_Exn.raise uu____12092)))
end
| uu____12129 -> begin
()
end));
(

let uu____12131 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____12131) with
| true -> begin
(

let uu____12132 = (FStar_TypeChecker_Normalize.term_to_string env exp1)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____12132))
end
| uu____12133 -> begin
()
end));
(

let p1 = (FStar_TypeChecker_Util.decorate_pattern env p exp1)
in ((p1), (pat_bvs1), (pat_env), (exp1), (norm_exp)));
))))))
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

let uu____12141 = (

let uu____12148 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____12148 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____12141) with
| (scrutinee_env, uu____12172) -> begin
(

let uu____12177 = (tc_pat true pat_t pattern)
in (match (uu____12177) with
| (pattern1, pat_bvs1, pat_env, pat_exp, norm_pat_exp) -> begin
(

let uu____12215 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____12237 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____12237) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____12250 -> begin
(

let uu____12251 = (

let uu____12258 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_Syntax_Util.t_bool)
in (tc_term uu____12258 e))
in (match (uu____12251) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____12215) with
| (when_clause1, g_when) -> begin
(

let uu____12292 = (tc_term pat_env branch_exp)
in (match (uu____12292) with
| (branch_exp1, c, g_branch) -> begin
(

let when_condition = (match (when_clause1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____12324 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____12324))
end)
in (

let uu____12327 = (

let eqs = (

let uu____12337 = (

let uu____12338 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12338)))
in (match (uu____12337) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12341 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____12345) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____12362) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____12363) -> begin
FStar_Pervasives_Native.None
end
| uu____12364 -> begin
(

let uu____12365 = (

let uu____12366 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____12366 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____12365))
end))
end))
in (

let uu____12367 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch)
in (match (uu____12367) with
| (c1, g_branch1) -> begin
(

let uu____12382 = (match (((eqs), (when_condition))) with
| uu____12395 when (

let uu____12404 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12404))) -> begin
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

let uu____12416 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____12417 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____12416), (uu____12417))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____12426 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____12426))
in (

let uu____12427 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____12428 = (

let uu____12429 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____12429 g_when))
in ((uu____12427), (uu____12428))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____12437 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____12437), (g_when)))))
end)
in (match (uu____12382) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let uu____12449 = (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak)
in (

let uu____12450 = (FStar_TypeChecker_Rel.close_guard env binders g_when_weak)
in ((uu____12449), (uu____12450), (g_branch1)))))
end))
end)))
in (match (uu____12327) with
| (c1, g_when1, g_branch1) -> begin
(

let branch_guard = (

let uu____12471 = (

let uu____12472 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12472)))
in (match (uu____12471) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____12473 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____12502 = (

let uu____12503 = (

let uu____12504 = (

let uu____12507 = (

let uu____12514 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____12514))
in (FStar_Pervasives_Native.snd uu____12507))
in (FStar_List.length uu____12504))
in (uu____12503 > (Prims.parse_int "1")))
in (match (uu____12502) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____12520 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____12520) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____12541 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____12556 = (

let uu____12557 = (

let uu____12558 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____12558)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____12557))
in (uu____12556 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____12561 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____12561)::[])))
end)))
end
| uu____12562 -> begin
[]
end)))
in (

let fail = (fun uu____12566 -> (

let uu____12567 = (

let uu____12568 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____12569 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____12570 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____12568 uu____12569 uu____12570))))
in (failwith uu____12567)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____12581) -> begin
(head_constructor t1)
end
| uu____12586 -> begin
(fail ())
end))
in (

let pat_exp2 = (

let uu____12588 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____12588 FStar_Syntax_Util.unmeta))
in (match (pat_exp2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____12591) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12608); FStar_Syntax_Syntax.pos = uu____12609; FStar_Syntax_Syntax.vars = uu____12610}, uu____12611) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_name (uu____12648) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (c2) -> begin
(

let uu____12650 = (

let uu____12651 = (tc_constant pat_exp2.FStar_Syntax_Syntax.pos c2)
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____12651 scrutinee_tm1 pat_exp2))
in (uu____12650)::[])
end
| FStar_Syntax_Syntax.Tm_uinst (uu____12652) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____12660 = (

let uu____12661 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____12661)))
in (match (uu____12660) with
| true -> begin
[]
end
| uu____12664 -> begin
(

let uu____12665 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____12665))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____12668) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____12670 = (

let uu____12671 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____12671)))
in (match (uu____12670) with
| true -> begin
[]
end
| uu____12674 -> begin
(

let uu____12675 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____12675))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let f = (head_constructor head1)
in (

let uu____12701 = (

let uu____12702 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____12702)))
in (match (uu____12701) with
| true -> begin
[]
end
| uu____12705 -> begin
(

let sub_term_guards = (

let uu____12709 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____12741 -> (match (uu____12741) with
| (ei, uu____12751) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____12757 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____12757) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____12778 -> begin
(

let sub_term = (

let uu____12792 = (

let uu____12793 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____12794 = (

let uu____12795 = (FStar_Syntax_Syntax.as_arg scrutinee_tm1)
in (uu____12795)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____12793 uu____12794)))
in (uu____12792 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____12709 FStar_List.flatten))
in (

let uu____12804 = (discriminate scrutinee_tm1 f)
in (FStar_List.append uu____12804 sub_term_guards)))
end)))
end
| uu____12807 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pat -> (

let uu____12819 = (

let uu____12820 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12820)))
in (match (uu____12819) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____12821 -> begin
(

let t = (

let uu____12823 = (build_branch_guard scrutinee_tm1 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____12823))
in (

let uu____12828 = (FStar_Syntax_Util.type_u ())
in (match (uu____12828) with
| (k, uu____12834) -> begin
(

let uu____12835 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____12835) with
| (t1, uu____12843, uu____12844) -> begin
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

let guard = (FStar_TypeChecker_Rel.conj_guard g_when1 g_branch1)
in ((

let uu____12850 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____12850) with
| true -> begin
(

let uu____12851 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____12851))
end
| uu____12852 -> begin
()
end));
(

let uu____12853 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in ((uu____12853), (branch_guard), (c1), (guard)));
)))
end)))
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

let uu____12879 = (check_let_bound_def true env1 lb)
in (match (uu____12879) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____12901 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____12918 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____12918), (univ_vars1), (c1)))
end
| uu____12919 -> begin
(

let g11 = (

let uu____12921 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____12921 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____12925 = (

let uu____12938 = (

let uu____12953 = (

let uu____12962 = (

let uu____12975 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____12975)))
in (uu____12962)::[])
in (FStar_TypeChecker_Util.generalize env1 false uu____12953))
in (FStar_List.hd uu____12938))
in (match (uu____12925) with
| (uu____13028, univs1, e11, c11, gvs) -> begin
(

let g12 = (FStar_All.pipe_left (FStar_TypeChecker_Rel.map_guard g11) (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env1))
in (

let g13 = (FStar_TypeChecker_Rel.abstract_guard_n gvs g12)
in ((g13), (e11), (univs1), ((FStar_Syntax_Util.lcomp_of_comp c11)))))
end)))
end)
in (match (uu____12901) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____13051 = (

let uu____13058 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____13058) with
| true -> begin
(

let uu____13065 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____13065) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____13086 -> begin
((

let uu____13088 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.warn uu____13088 FStar_TypeChecker_Err.top_level_effect));
(

let uu____13089 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____13089), (c12)));
)
end)
end))
end
| uu____13096 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____13099 = (c11.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right uu____13099 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env1)))
in (

let e21 = (

let uu____13107 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____13107) with
| true -> begin
e2
end
| uu____13110 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end))
in ((e21), (c))));
)
end))
in (match (uu____13051) with
| (e21, c12) -> begin
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit)
in (

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e11)
in (

let uu____13131 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in ((uu____13131), ((FStar_Syntax_Util.lcomp_of_comp cres)), (FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| uu____13146 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___146_13177 = env1
in {FStar_TypeChecker_Env.solver = uu___146_13177.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___146_13177.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___146_13177.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___146_13177.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___146_13177.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___146_13177.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___146_13177.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___146_13177.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___146_13177.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___146_13177.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___146_13177.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___146_13177.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___146_13177.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___146_13177.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___146_13177.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___146_13177.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___146_13177.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___146_13177.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___146_13177.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___146_13177.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___146_13177.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___146_13177.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___146_13177.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___146_13177.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___146_13177.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___146_13177.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___146_13177.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___146_13177.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___146_13177.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___146_13177.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___146_13177.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___146_13177.FStar_TypeChecker_Env.dsenv})
in (

let uu____13178 = (

let uu____13189 = (

let uu____13190 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____13190 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____13189 lb))
in (match (uu____13178) with
| (e1, uu____13212, c1, g1, annotated) -> begin
(

let x = (

let uu___147_13217 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___147_13217.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___147_13217.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____13218 = (

let uu____13223 = (

let uu____13224 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____13224)::[])
in (FStar_Syntax_Subst.open_term uu____13223 e2))
in (match (uu____13218) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let uu____13243 = (

let uu____13250 = (FStar_TypeChecker_Env.push_bv env2 x1)
in (tc_term uu____13250 e21))
in (match (uu____13243) with
| (e22, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env2 (FStar_Pervasives_Native.Some (e1)) c1 ((FStar_Pervasives_Native.Some (x1)), (c2)))
in (

let e11 = (FStar_TypeChecker_Util.maybe_lift env2 e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e23 = (FStar_TypeChecker_Util.maybe_lift env2 e22 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let lb1 = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x1)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e11)
in (

let e3 = (

let uu____13269 = (

let uu____13272 = (

let uu____13273 = (

let uu____13286 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____13286)))
in FStar_Syntax_Syntax.Tm_let (uu____13273))
in (FStar_Syntax_Syntax.mk uu____13272))
in (uu____13269 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____13300 = (

let uu____13301 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____13302 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____13301 c1.FStar_Syntax_Syntax.res_typ uu____13302 e11)))
in (FStar_All.pipe_left (fun _0_43 -> FStar_TypeChecker_Common.NonTrivial (_0_43)) uu____13300))
in (

let g21 = (

let uu____13304 = (

let uu____13305 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____13305 g2))
in (FStar_TypeChecker_Rel.close_guard env2 xb uu____13304))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g21)
in (

let uu____13307 = (

let uu____13308 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____13308))
in (match (uu____13307) with
| true -> begin
(

let tt = (

let uu____13318 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____13318 FStar_Option.get))
in ((

let uu____13324 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____13324) with
| true -> begin
(

let uu____13325 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____13326 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____13325 uu____13326)))
end
| uu____13327 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____13328 -> begin
(

let t = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____13331 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____13331) with
| true -> begin
(

let uu____13332 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____13333 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____13332 uu____13333)))
end
| uu____13334 -> begin
()
end));
((e4), ((

let uu___148_13336 = cres
in {FStar_Syntax_Syntax.eff_name = uu___148_13336.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___148_13336.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___148_13336.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____13337 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____13369 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____13369) with
| (lbs1, e21) -> begin
(

let uu____13388 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____13388) with
| (env0, topt) -> begin
(

let uu____13407 = (build_let_rec_env true env0 lbs1)
in (match (uu____13407) with
| (lbs2, rec_env) -> begin
(

let uu____13426 = (check_let_recs rec_env lbs2)
in (match (uu____13426) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____13446 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g_lbs)
in (FStar_All.pipe_right uu____13446 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (

let uu____13452 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____13452 (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((Prims.op_Equality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
lb
end
| uu____13484 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef)
end)))))
end
| uu____13485 -> begin
(

let ecs = (

let uu____13501 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____13541 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____13541))))))
in (FStar_TypeChecker_Util.generalize env1 true uu____13501))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____13590 -> (match (uu____13590) with
| (x, uvs, e, c, gvs) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (

let uu____13637 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____13637))
in (

let uu____13642 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____13642) with
| (lbs5, e22) -> begin
((

let uu____13662 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____13662 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____13663 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____13663), (cres), (FStar_TypeChecker_Rel.trivial_guard)));
)
end))))))
end))
end))
end))
end))
end
| uu____13676 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____13708 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____13708) with
| (lbs1, e21) -> begin
(

let uu____13727 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____13727) with
| (env0, topt) -> begin
(

let uu____13746 = (build_let_rec_env false env0 lbs1)
in (match (uu____13746) with
| (lbs2, rec_env) -> begin
(

let uu____13765 = (check_let_recs rec_env lbs2)
in (match (uu____13765) with
| (lbs3, g_lbs) -> begin
(

let uu____13784 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___149_13807 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___149_13807.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___149_13807.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___150_13809 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___150_13809.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___150_13809.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___150_13809.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___150_13809.FStar_Syntax_Syntax.lbdef})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____13784) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____13836 = (tc_term env2 e21)
in (match (uu____13836) with
| (e22, cres, g2) -> begin
(

let guard = (

let uu____13853 = (

let uu____13854 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Rel.close_guard env2 uu____13854 g2))
in (FStar_TypeChecker_Rel.conj_guard g_lbs uu____13853))
in (

let cres1 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres)
in (

let tres = (norm env2 cres1.FStar_Syntax_Syntax.res_typ)
in (

let cres2 = (

let uu___151_13858 = cres1
in {FStar_Syntax_Syntax.eff_name = uu___151_13858.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___151_13858.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___151_13858.FStar_Syntax_Syntax.comp})
in (

let uu____13859 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____13859) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____13895) -> begin
((e), (cres2), (guard))
end
| FStar_Pervasives_Native.None -> begin
(

let tres1 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (

let cres3 = (

let uu___152_13900 = cres2
in {FStar_Syntax_Syntax.eff_name = uu___152_13900.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___152_13900.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___152_13900.FStar_Syntax_Syntax.comp})
in ((e), (cres3), (guard))))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| uu____13903 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let uu____13932 = (FStar_Options.ml_ish ())
in (match (uu____13932) with
| true -> begin
false
end
| uu____13933 -> begin
(

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____13935 = (

let uu____13940 = (

let uu____13941 = (FStar_Syntax_Subst.compress t)
in uu____13941.FStar_Syntax_Syntax.n)
in (

let uu____13944 = (

let uu____13945 = (FStar_Syntax_Subst.compress lbdef)
in uu____13945.FStar_Syntax_Syntax.n)
in ((uu____13940), (uu____13944))))
in (match (uu____13935) with
| (FStar_Syntax_Syntax.Tm_arrow (formals, c), FStar_Syntax_Syntax.Tm_abs (actuals, uu____13951, uu____13952)) -> begin
(

let actuals1 = (

let uu____13990 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____13990 actuals))
in ((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____14010 -> begin
(

let uu____14011 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____14011))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____14028 -> begin
(

let uu____14029 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____14029))
end))
in (

let msg = (

let uu____14037 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____14038 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____14037 uu____14038 formals_msg actuals_msg)))
in (FStar_Exn.raise (FStar_Errors.Error (((msg), (lbdef.FStar_Syntax_Syntax.pos))))))))
end
| uu____14039 -> begin
()
end);
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)));
))
end
| uu____14045 -> begin
(

let uu____14050 = (

let uu____14051 = (

let uu____14056 = (

let uu____14057 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____14058 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____14057 uu____14058)))
in ((uu____14056), (lbtyp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____14051))
in (FStar_Exn.raise uu____14050))
end)))
end)))
in (

let uu____14059 = (FStar_List.fold_left (fun uu____14085 lb -> (match (uu____14085) with
| (lbs1, env1) -> begin
(

let uu____14105 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____14105) with
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
| uu____14124 -> begin
(

let uu____14125 = (

let uu____14132 = (

let uu____14133 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14133))
in (tc_check_tot_or_gtot_term (

let uu___153_14144 = env0
in {FStar_TypeChecker_Env.solver = uu___153_14144.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___153_14144.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___153_14144.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___153_14144.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___153_14144.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___153_14144.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___153_14144.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___153_14144.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___153_14144.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___153_14144.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___153_14144.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___153_14144.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___153_14144.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___153_14144.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___153_14144.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___153_14144.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___153_14144.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___153_14144.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___153_14144.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___153_14144.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___153_14144.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___153_14144.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___153_14144.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___153_14144.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___153_14144.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___153_14144.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___153_14144.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___153_14144.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___153_14144.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___153_14144.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___153_14144.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___153_14144.FStar_TypeChecker_Env.dsenv}) t uu____14132))
in (match (uu____14125) with
| (t1, uu____14146, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((

let uu____14150 = (FStar_TypeChecker_Rel.discharge_guard env2 g1)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____14150));
(norm env0 t1);
))
end))
end)
in (

let env3 = (

let uu____14152 = ((termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1) && (FStar_TypeChecker_Env.should_verify env2))
in (match (uu____14152) with
| true -> begin
(

let uu___154_14153 = env2
in {FStar_TypeChecker_Env.solver = uu___154_14153.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___154_14153.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___154_14153.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___154_14153.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___154_14153.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___154_14153.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___154_14153.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___154_14153.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___154_14153.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___154_14153.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___154_14153.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___154_14153.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___154_14153.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___154_14153.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___154_14153.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___154_14153.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___154_14153.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___154_14153.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___154_14153.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___154_14153.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___154_14153.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___154_14153.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___154_14153.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___154_14153.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___154_14153.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___154_14153.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___154_14153.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___154_14153.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___154_14153.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___154_14153.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___154_14153.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___154_14153.FStar_TypeChecker_Env.dsenv})
end
| uu____14166 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname (([]), (t1)))
end))
in (

let lb1 = (

let uu___155_14170 = lb
in {FStar_Syntax_Syntax.lbname = uu___155_14170.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___155_14170.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb1)::lbs1), (env3)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____14059) with
| (lbs1, env1) -> begin
(((FStar_List.rev lbs1)), (env1))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____14193 = (

let uu____14202 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> ((

let uu____14231 = (

let uu____14232 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____14232.FStar_Syntax_Syntax.n)
in (match (uu____14231) with
| FStar_Syntax_Syntax.Tm_abs (uu____14235) -> begin
()
end
| uu____14252 -> begin
(

let uu____14253 = (

let uu____14254 = (

let uu____14259 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (("Only function literals may be defined recursively"), (uu____14259)))
in FStar_Errors.Error (uu____14254))
in (FStar_Exn.raise uu____14253))
end));
(

let uu____14260 = (

let uu____14267 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____14267 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____14260) with
| (e, c, g) -> begin
((

let uu____14276 = (

let uu____14277 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____14277)))
in (match (uu____14276) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____14278 -> begin
()
end));
(

let lb1 = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e)
in ((lb1), (g)));
)
end));
))))
in (FStar_All.pipe_right uu____14202 FStar_List.unzip))
in (match (uu____14193) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____14326 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____14326) with
| (env1, uu____14344) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____14352 = (check_lbtyp top_level env lb)
in (match (uu____14352) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (Prims.op_disEquality univ_vars1 []))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____14391 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____14396 = (tc_maybe_toplevel_term (

let uu___156_14405 = env11
in {FStar_TypeChecker_Env.solver = uu___156_14405.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___156_14405.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___156_14405.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___156_14405.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___156_14405.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___156_14405.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___156_14405.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___156_14405.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___156_14405.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___156_14405.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___156_14405.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___156_14405.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___156_14405.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___156_14405.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___156_14405.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___156_14405.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___156_14405.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___156_14405.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___156_14405.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___156_14405.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___156_14405.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___156_14405.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___156_14405.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___156_14405.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___156_14405.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___156_14405.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___156_14405.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___156_14405.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___156_14405.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___156_14405.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___156_14405.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___156_14405.FStar_TypeChecker_Env.dsenv}) e11)
in (match (uu____14396) with
| (e12, c1, g1) -> begin
(

let uu____14419 = (

let uu____14424 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____14428 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____14424 e12 c1 wf_annot))
in (match (uu____14419) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____14443 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14443) with
| true -> begin
(

let uu____14444 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____14445 = (FStar_Syntax_Print.term_to_string c11.FStar_Syntax_Syntax.res_typ)
in (

let uu____14446 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" uu____14444 uu____14445 uu____14446))))
end
| uu____14447 -> begin
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
((match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end
| uu____14483 -> begin
()
end);
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____14490 -> begin
(

let uu____14491 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____14491) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____14540 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____14540)))
end
| uu____14547 -> begin
(

let uu____14548 = (FStar_Syntax_Util.type_u ())
in (match (uu____14548) with
| (k, uu____14568) -> begin
(

let uu____14569 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____14569) with
| (t2, uu____14591, g) -> begin
((

let uu____14594 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____14594) with
| true -> begin
(

let uu____14595 = (

let uu____14596 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____14596))
in (

let uu____14597 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____14595 uu____14597)))
end
| uu____14598 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____14600 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____14600))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____14608 -> (match (uu____14608) with
| (x, imp) -> begin
(

let uu____14627 = (FStar_Syntax_Util.type_u ())
in (match (uu____14627) with
| (tu, u) -> begin
((

let uu____14647 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14647) with
| true -> begin
(

let uu____14648 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14649 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14650 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____14648 uu____14649 uu____14650))))
end
| uu____14651 -> begin
()
end));
(

let uu____14652 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____14652) with
| (t, uu____14672, g) -> begin
(

let x1 = (((

let uu___157_14680 = x
in {FStar_Syntax_Syntax.ppname = uu___157_14680.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___157_14680.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____14682 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____14682) with
| true -> begin
(

let uu____14683 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____14684 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____14683 uu____14684)))
end
| uu____14685 -> begin
()
end));
(

let uu____14686 = (push_binding env x1)
in ((x1), (uu____14686), (g), (u)));
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

let uu____14776 = (tc_binder env1 b)
in (match (uu____14776) with
| (b1, env', g, u) -> begin
(

let uu____14817 = (aux env' bs2)
in (match (uu____14817) with
| (bs3, env'1, g', us) -> begin
(

let uu____14870 = (

let uu____14871 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____14871))
in (((b1)::bs3), (env'1), (uu____14870), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____14956 uu____14957 -> (match (((uu____14956), (uu____14957))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____15026 = (tc_term env1 t)
in (match (uu____15026) with
| (t1, uu____15044, g') -> begin
(

let uu____15046 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____15046)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____15088 -> (match (uu____15088) with
| (pats1, g) -> begin
(

let uu____15113 = (tc_args env p)
in (match (uu____15113) with
| (args, g') -> begin
(

let uu____15126 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats1), (uu____15126)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____15139 = (tc_maybe_toplevel_term env e)
in (match (uu____15139) with
| (e1, c, g) -> begin
(

let uu____15155 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____15155) with
| true -> begin
((e1), (c), (g))
end
| uu____15162 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (c.FStar_Syntax_Syntax.comp ())
in (

let c2 = (norm_c env c1)
in (

let uu____15168 = (

let uu____15173 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____15173) with
| true -> begin
(

let uu____15178 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____15178), (false)))
end
| uu____15179 -> begin
(

let uu____15180 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____15180), (true)))
end))
in (match (uu____15168) with
| (target_comp, allow_ghost) -> begin
(

let uu____15189 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____15189) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____15199 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in ((e1), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (uu____15199)))
end
| uu____15200 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____15209 = (

let uu____15210 = (

let uu____15215 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in ((uu____15215), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____15210))
in (FStar_Exn.raise uu____15209))
end
| uu____15222 -> begin
(

let uu____15223 = (

let uu____15224 = (

let uu____15229 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in ((uu____15229), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____15224))
in (FStar_Exn.raise uu____15223))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____15248 = (tc_tot_or_gtot_term env t)
in (match (uu____15248) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____15278 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____15278) with
| true -> begin
(

let uu____15279 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____15279))
end
| uu____15280 -> begin
()
end));
(

let env1 = (

let uu___158_15282 = env
in {FStar_TypeChecker_Env.solver = uu___158_15282.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___158_15282.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___158_15282.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___158_15282.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___158_15282.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___158_15282.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___158_15282.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___158_15282.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___158_15282.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___158_15282.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___158_15282.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___158_15282.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___158_15282.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___158_15282.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___158_15282.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___158_15282.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___158_15282.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___158_15282.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___158_15282.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___158_15282.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___158_15282.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___158_15282.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___158_15282.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___158_15282.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___158_15282.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___158_15282.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___158_15282.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___158_15282.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___158_15282.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___158_15282.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___158_15282.FStar_TypeChecker_Env.dsenv})
in (

let uu____15287 = (FStar_All.try_with (fun uu___160_15301 -> (match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)) (fun uu___159_15312 -> (match (uu___159_15312) with
| FStar_Errors.Error (msg, uu____15320) -> begin
(

let uu____15321 = (

let uu____15322 = (

let uu____15327 = (FStar_TypeChecker_Env.get_range env1)
in (((Prims.strcat "Implicit argument: " msg)), (uu____15327)))
in FStar_Errors.Error (uu____15322))
in (FStar_Exn.raise uu____15321))
end)))
in (match (uu____15287) with
| (t, c, g) -> begin
(

let uu____15343 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____15343) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____15352 -> begin
(

let uu____15353 = (

let uu____15354 = (

let uu____15359 = (

let uu____15360 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____15360))
in (

let uu____15361 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____15359), (uu____15361))))
in FStar_Errors.Error (uu____15354))
in (FStar_Exn.raise uu____15353))
end))
end)));
))


let level_of_type_fail : 'Auu____15376 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  'Auu____15376 = (fun env e t -> (

let uu____15389 = (

let uu____15390 = (

let uu____15395 = (

let uu____15396 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____15396 t))
in (

let uu____15397 = (FStar_TypeChecker_Env.get_range env)
in ((uu____15395), (uu____15397))))
in FStar_Errors.Error (uu____15390))
in (FStar_Exn.raise uu____15389)))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____15417 = (

let uu____15418 = (FStar_Syntax_Util.unrefine t1)
in uu____15418.FStar_Syntax_Syntax.n)
in (match (uu____15417) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____15422 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____15424 -> begin
(

let uu____15425 = (FStar_Syntax_Util.type_u ())
in (match (uu____15425) with
| (t_u, u) -> begin
(

let env1 = (

let uu___161_15433 = env
in {FStar_TypeChecker_Env.solver = uu___161_15433.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___161_15433.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___161_15433.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___161_15433.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___161_15433.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___161_15433.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___161_15433.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___161_15433.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___161_15433.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___161_15433.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___161_15433.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___161_15433.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___161_15433.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___161_15433.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___161_15433.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___161_15433.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___161_15433.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___161_15433.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___161_15433.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___161_15433.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___161_15433.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___161_15433.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___161_15433.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___161_15433.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___161_15433.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___161_15433.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___161_15433.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___161_15433.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___161_15433.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___161_15433.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___161_15433.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___161_15433.FStar_TypeChecker_Env.dsenv})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____15437 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____15437))
end
| uu____15438 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____15449 = (

let uu____15450 = (FStar_Syntax_Subst.compress e)
in uu____15450.FStar_Syntax_Syntax.n)
in (match (uu____15449) with
| FStar_Syntax_Syntax.Tm_bvar (uu____15455) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____15460) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____15487) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____15503) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____15526, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____15553) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____15560 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____15560) with
| ((uu____15571, t), uu____15573) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____15578, (FStar_Util.Inl (t), uu____15580), uu____15581) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____15628, (FStar_Util.Inr (c), uu____15630), uu____15631) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____15681; FStar_Syntax_Syntax.vars = uu____15682}, us) -> begin
(

let uu____15688 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____15688) with
| ((us', t), uu____15701) -> begin
((match ((Prims.op_disEquality (FStar_List.length us) (FStar_List.length us'))) with
| true -> begin
(

let uu____15707 = (

let uu____15708 = (

let uu____15713 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____15713)))
in FStar_Errors.Error (uu____15708))
in (FStar_Exn.raise uu____15707))
end
| uu____15714 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____15729 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____15730) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____15740) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____15763 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____15763) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____15783 -> (match (uu____15783) with
| (b, uu____15789) -> begin
(

let uu____15790 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____15790))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____15795 = (universe_of_aux env res)
in (level_of_type env res uu____15795)))
in (

let u_c = (

let uu____15797 = (FStar_TypeChecker_Env.effect_repr env c1 u_res)
in (match (uu____15797) with
| FStar_Pervasives_Native.None -> begin
u_res
end
| FStar_Pervasives_Native.Some (trepr) -> begin
(

let uu____15801 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____15801))
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
| FStar_Syntax_Syntax.Tm_bvar (uu____15894) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____15909) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____15948) -> begin
(

let uu____15949 = (universe_of_aux env hd3)
in ((uu____15949), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____15962) -> begin
(

let uu____15963 = (universe_of_aux env hd3)
in ((uu____15963), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____15976) -> begin
(

let uu____15993 = (universe_of_aux env hd3)
in ((uu____15993), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____16006) -> begin
(

let uu____16013 = (universe_of_aux env hd3)
in ((uu____16013), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____16026) -> begin
(

let uu____16053 = (universe_of_aux env hd3)
in ((uu____16053), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____16066) -> begin
(

let uu____16073 = (universe_of_aux env hd3)
in ((uu____16073), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____16086) -> begin
(

let uu____16087 = (universe_of_aux env hd3)
in ((uu____16087), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____16100) -> begin
(

let uu____16113 = (universe_of_aux env hd3)
in ((uu____16113), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____16126) -> begin
(

let uu____16133 = (universe_of_aux env hd3)
in ((uu____16133), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____16146) -> begin
(

let uu____16147 = (universe_of_aux env hd3)
in ((uu____16147), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____16160, (hd4)::uu____16162) -> begin
(

let uu____16227 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____16227) with
| (uu____16242, uu____16243, hd5) -> begin
(

let uu____16261 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____16261) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____16312 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____16314 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____16314) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____16365 -> begin
(

let uu____16366 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____16366) with
| (env1, uu____16388) -> begin
(

let env2 = (

let uu___162_16394 = env1
in {FStar_TypeChecker_Env.solver = uu___162_16394.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___162_16394.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___162_16394.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___162_16394.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___162_16394.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___162_16394.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___162_16394.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___162_16394.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___162_16394.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___162_16394.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___162_16394.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___162_16394.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___162_16394.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___162_16394.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___162_16394.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___162_16394.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___162_16394.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___162_16394.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___162_16394.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___162_16394.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___162_16394.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___162_16394.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___162_16394.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___162_16394.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___162_16394.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___162_16394.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___162_16394.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___162_16394.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___162_16394.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___162_16394.FStar_TypeChecker_Env.dsenv})
in ((

let uu____16396 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____16396) with
| true -> begin
(

let uu____16397 = (

let uu____16398 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____16398))
in (

let uu____16399 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____16397 uu____16399)))
end
| uu____16400 -> begin
()
end));
(

let uu____16401 = (tc_term env2 hd3)
in (match (uu____16401) with
| (uu____16422, {FStar_Syntax_Syntax.eff_name = uu____16423; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____16425; FStar_Syntax_Syntax.comp = uu____16426}, g) -> begin
((

let uu____16437 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____16437 FStar_Pervasives.ignore));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____16448 = (type_of_head true hd1 args)
in (match (uu____16448) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____16488 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____16488) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____16531 -> begin
(

let uu____16532 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____16532))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____16535, (hd1)::uu____16537) -> begin
(

let uu____16602 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____16602) with
| (uu____16605, uu____16606, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____16624, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____16669 = (universe_of_aux env e)
in (level_of_type env e uu____16669)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____16690 = (tc_binders env tps)
in (match (uu____16690) with
| (tps1, env1, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
((tps1), (env1), (us));
)
end)))




