
open Prims
open FStar_Pervasives

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___93_5 = env
in {FStar_TypeChecker_Env.solver = uu___93_5.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___93_5.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___93_5.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___93_5.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___93_5.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___93_5.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___93_5.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___93_5.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___93_5.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___93_5.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___93_5.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___93_5.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___93_5.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___93_5.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___93_5.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___93_5.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___93_5.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___93_5.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___93_5.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___93_5.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___93_5.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___93_5.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___93_5.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___93_5.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___93_5.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___93_5.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___93_5.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___93_5.FStar_TypeChecker_Env.identifier_info}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___94_10 = env
in {FStar_TypeChecker_Env.solver = uu___94_10.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___94_10.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___94_10.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___94_10.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___94_10.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___94_10.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___94_10.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___94_10.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___94_10.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___94_10.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___94_10.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___94_10.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___94_10.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___94_10.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___94_10.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___94_10.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___94_10.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___94_10.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___94_10.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___94_10.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___94_10.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___94_10.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___94_10.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___94_10.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___94_10.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___94_10.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___94_10.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___94_10.FStar_TypeChecker_Env.identifier_info}))


let mk_lex_list : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v1 tl1 -> (

let r = (match ((tl1.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
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


let is_eq : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___88_57 -> (match (uu___88_57) with
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

let uu___95_226 = lc
in {FStar_Syntax_Syntax.eff_name = uu___95_226.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___95_226.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____229 -> (

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
(FStar_Util.print_string "Expected type is None")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____713 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____713))
end)))


let check_smt_pat : 'Auu____724 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * 'Auu____724) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.unit = (fun env t bs c -> (

let uu____757 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____757) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____758; FStar_Syntax_Syntax.effect_name = uu____759; FStar_Syntax_Syntax.result_typ = uu____760; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____764))::[]; FStar_Syntax_Syntax.flags = uu____765}) -> begin
(

let pat_vars = (

let uu____813 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names uu____813))
in (

let uu____814 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____841 -> (match (uu____841) with
| (b, uu____847) -> begin
(

let uu____848 = (FStar_Util.set_mem b pat_vars)
in (not (uu____848)))
end))))
in (match (uu____814) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____854) -> begin
(

let uu____859 = (

let uu____860 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____860))
in (FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____859))
end)))
end
| uu____861 -> begin
(failwith "Impossible")
end)
end
| uu____862 -> begin
()
end)))


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (

let uu____891 = (

let uu____892 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____892)))
in (match (uu____891) with
| true -> begin
env.FStar_TypeChecker_Env.letrecs
end
| uu____899 -> begin
(match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env1 = (

let uu___96_923 = env
in {FStar_TypeChecker_Env.solver = uu___96_923.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_923.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_923.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_923.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___96_923.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_923.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_923.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_923.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_923.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_923.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_923.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_923.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___96_923.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___96_923.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___96_923.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___96_923.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_923.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___96_923.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___96_923.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___96_923.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___96_923.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_923.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_923.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___96_923.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___96_923.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___96_923.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___96_923.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___96_923.FStar_TypeChecker_Env.identifier_info})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____957 -> (match (uu____957) with
| (b, uu____965) -> begin
(

let t = (

let uu____967 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____967))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____970) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____971) -> begin
[]
end
| uu____984 -> begin
(

let uu____985 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____985)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____990 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____990) with
| (head1, uu____1006) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____1028 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____1032 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___89_1041 -> (match (uu___89_1041) with
| FStar_Syntax_Syntax.DECREASES (uu____1042) -> begin
true
end
| uu____1045 -> begin
false
end))))
in (match (uu____1032) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____1049 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____1058 -> begin
(mk_lex_list xs)
end))
end))))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____1075 -> (match (uu____1075) with
| (l, t) -> begin
(

let uu____1088 = (

let uu____1089 = (FStar_Syntax_Subst.compress t)
in uu____1089.FStar_Syntax_Syntax.n)
in (match (uu____1088) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____1148 -> (match (uu____1148) with
| (x, imp) -> begin
(

let uu____1159 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____1159) with
| true -> begin
(

let uu____1164 = (

let uu____1165 = (

let uu____1168 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____1168))
in (FStar_Syntax_Syntax.new_bv uu____1165 x.FStar_Syntax_Syntax.sort))
in ((uu____1164), (imp)))
end
| uu____1169 -> begin
((x), (imp))
end))
end))))
in (

let uu____1170 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____1170) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____1187 = (

let uu____1188 = (

let uu____1189 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____1190 = (

let uu____1193 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____1193)::[])
in (uu____1189)::uu____1190))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____1188))
in (uu____1187 FStar_Pervasives_Native.None r))
in (

let uu____1196 = (FStar_Util.prefix formals2)
in (match (uu____1196) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___97_1241 = last1
in (

let uu____1242 = (FStar_Syntax_Util.refine last1 precedes1)
in {FStar_Syntax_Syntax.ppname = uu___97_1241.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___97_1241.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1242}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____1268 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1268) with
| true -> begin
(

let uu____1269 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____1270 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1271 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____1269 uu____1270 uu____1271))))
end
| uu____1272 -> begin
()
end));
((l), (t'));
))))
end))))
end)))
end
| uu____1275 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let uu___98_1706 = env
in {FStar_TypeChecker_Env.solver = uu___98_1706.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___98_1706.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___98_1706.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___98_1706.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___98_1706.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___98_1706.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___98_1706.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___98_1706.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___98_1706.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___98_1706.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___98_1706.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___98_1706.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___98_1706.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___98_1706.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___98_1706.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___98_1706.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___98_1706.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___98_1706.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___98_1706.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___98_1706.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___98_1706.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___98_1706.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___98_1706.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___98_1706.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___98_1706.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___98_1706.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___98_1706.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___98_1706.FStar_TypeChecker_Env.identifier_info}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (match ((e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____1716 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____1718 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1718) with
| true -> begin
(

let uu____1719 = (

let uu____1720 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1720))
in (

let uu____1721 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" uu____1719 uu____1721)))
end
| uu____1722 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1730) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1761) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1768) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1785) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____1786) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1787) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1788) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____1789) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1806) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____1819) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____1826) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____1832 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____1832) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___99_1849 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___99_1849.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___99_1849.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___99_1849.FStar_TypeChecker_Env.implicits})
in ((e2), (c), (g1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____1866 = (FStar_Syntax_Util.type_u ())
in (match (uu____1866) with
| (t, u) -> begin
(

let uu____1879 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____1879) with
| (e2, c, g) -> begin
(

let uu____1895 = (

let uu____1910 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____1910) with
| (env2, uu____1932) -> begin
(tc_pats env2 pats)
end))
in (match (uu____1895) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___100_1966 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___100_1966.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___100_1966.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___100_1966.FStar_TypeChecker_Env.implicits})
in (

let uu____1967 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____1970 = (FStar_TypeChecker_Rel.conj_guard g g'1)
in ((uu____1967), (c), (uu____1970)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____1978 = (

let uu____1979 = (FStar_Syntax_Subst.compress e1)
in uu____1979.FStar_Syntax_Syntax.n)
in (match (uu____1978) with
| FStar_Syntax_Syntax.Tm_let ((uu____1988, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____1990; FStar_Syntax_Syntax.lbtyp = uu____1991; FStar_Syntax_Syntax.lbeff = uu____1992; FStar_Syntax_Syntax.lbdef = e11})::[]), e2) -> begin
(

let uu____2017 = (

let uu____2024 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (tc_term uu____2024 e11))
in (match (uu____2017) with
| (e12, c1, g1) -> begin
(

let uu____2034 = (tc_term env1 e2)
in (match (uu____2034) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e3 = (

let uu____2058 = (

let uu____2061 = (

let uu____2062 = (

let uu____2075 = (

let uu____2082 = (

let uu____2085 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_Syntax_Syntax.t_unit), (e13)))
in (uu____2085)::[])
in ((false), (uu____2082)))
in ((uu____2075), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____2062))
in (FStar_Syntax_Syntax.mk uu____2061))
in (uu____2058 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2107 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e5), (c), (uu____2107)))))))))
end))
end))
end
| uu____2110 -> begin
(

let uu____2111 = (tc_term env1 e1)
in (match (uu____2111) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____2133)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____2150 = (tc_term env1 e1)
in (match (uu____2150) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____2174) -> begin
(

let uu____2221 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2221) with
| (env0, uu____2235) -> begin
(

let uu____2240 = (tc_comp env0 expected_c)
in (match (uu____2240) with
| (expected_c1, uu____2254, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c1)
in (

let uu____2259 = (

let uu____2266 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____2266 e1))
in (match (uu____2259) with
| (e2, c', g') -> begin
(

let uu____2276 = (

let uu____2283 = (

let uu____2288 = (c'.FStar_Syntax_Syntax.comp ())
in ((e2), (uu____2288)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____2283))
in (match (uu____2276) with
| (e3, expected_c2, g'') -> begin
(

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (t_res)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____2343 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____2343))
in (

let topt1 = (tc_tactic_opt env0 topt)
in (

let f1 = (match (topt1) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(FStar_TypeChecker_Rel.map_guard f (fun f1 -> (

let uu____2352 = (FStar_Syntax_Util.mk_squash f1)
in (FStar_TypeChecker_Common.mk_by_tactic tactic uu____2352))))
end)
in (

let uu____2353 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____2353) with
| (e5, c, f2) -> begin
(

let uu____2369 = (FStar_TypeChecker_Rel.conj_guard f1 f2)
in ((e5), (c), (uu____2369)))
end)))))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____2373) -> begin
(

let uu____2420 = (FStar_Syntax_Util.type_u ())
in (match (uu____2420) with
| (k, u) -> begin
(

let uu____2433 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____2433) with
| (t1, uu____2447, f) -> begin
(

let uu____2449 = (

let uu____2456 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____2456 e1))
in (match (uu____2449) with
| (e2, c, g) -> begin
(

let uu____2466 = (

let uu____2471 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____2475 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____2471 e2 c f))
in (match (uu____2466) with
| (c1, f1) -> begin
(

let uu____2484 = (

let uu____2491 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____2491 c1))
in (match (uu____2484) with
| (e3, c2, f2) -> begin
(

let uu____2531 = (

let uu____2532 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____2532))
in ((e3), (c2), (uu____2531)))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____2533; FStar_Syntax_Syntax.vars = uu____2534}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____2597 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2597) with
| (unary_op, uu____2619) -> begin
(

let head1 = (

let uu____2643 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____2643))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____2681)); FStar_Syntax_Syntax.pos = uu____2682; FStar_Syntax_Syntax.vars = uu____2683}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____2746 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2746) with
| (unary_op, uu____2768) -> begin
(

let head1 = (

let uu____2792 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____2792))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____2830; FStar_Syntax_Syntax.vars = uu____2831}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____2863 -> begin
()
end);
(

let uu____2864 = (

let uu____2871 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2871) with
| (env0, uu____2885) -> begin
(tc_term env0 e1)
end))
in (match (uu____2864) with
| (e2, c, g) -> begin
(

let uu____2899 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2899) with
| (reify_op, uu____2921) -> begin
(

let u_c = (

let uu____2943 = (tc_term env1 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____2943) with
| (uu____2950, c', uu____2952) -> begin
(

let uu____2953 = (

let uu____2954 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____2954.FStar_Syntax_Syntax.n)
in (match (uu____2953) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____2958 -> begin
(

let uu____2959 = (FStar_Syntax_Util.type_u ())
in (match (uu____2959) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2971 = (

let uu____2972 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____2973 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____2974 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____2972 uu____2973 uu____2974))))
in (failwith uu____2971))
end);
u;
))
end))
end))
end))
in (

let repr = (

let uu____2976 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_TypeChecker_Env.reify_comp env1 uu____2976 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____2997 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____2997 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____2998 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____2998) with
| (e4, c2, g') -> begin
(

let uu____3014 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e4), (c2), (uu____3014)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.pos = uu____3016; FStar_Syntax_Syntax.vars = uu____3017}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____3049 -> begin
()
end);
(

let no_reflect = (fun uu____3059 -> (

let uu____3060 = (

let uu____3061 = (

let uu____3066 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((uu____3066), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____3061))
in (FStar_Exn.raise uu____3060)))
in (

let uu____3073 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3073) with
| (reflect_op, uu____3095) -> begin
(

let uu____3116 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____3116) with
| FStar_Pervasives_Native.None -> begin
(no_reflect ())
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____3149 = (

let uu____3150 = (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____3150)))
in (match (uu____3149) with
| true -> begin
(no_reflect ())
end
| uu____3159 -> begin
(

let uu____3160 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3160) with
| (env_no_ex, topt) -> begin
(

let uu____3179 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____3199 = (

let uu____3202 = (

let uu____3203 = (

let uu____3218 = (

let uu____3221 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____3222 = (

let uu____3225 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____3225)::[])
in (uu____3221)::uu____3222))
in ((repr), (uu____3218)))
in FStar_Syntax_Syntax.Tm_app (uu____3203))
in (FStar_Syntax_Syntax.mk uu____3202))
in (uu____3199 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____3231 = (

let uu____3238 = (

let uu____3239 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____3239 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____3238 t))
in (match (uu____3231) with
| (t1, uu____3267, g) -> begin
(

let uu____3269 = (

let uu____3270 = (FStar_Syntax_Subst.compress t1)
in uu____3270.FStar_Syntax_Syntax.n)
in (match (uu____3269) with
| FStar_Syntax_Syntax.Tm_app (uu____3285, ((res, uu____3287))::((wp, uu____3289))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____3332 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____3179) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____3363 = (

let uu____3368 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____3368) with
| (e2, c, g) -> begin
((

let uu____3383 = (

let uu____3384 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____3384))
in (match (uu____3383) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 (((("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____3393 -> begin
()
end));
(

let uu____3394 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____3394) with
| FStar_Pervasives_Native.None -> begin
((

let uu____3402 = (

let uu____3409 = (

let uu____3414 = (

let uu____3415 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____3416 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____3415 uu____3416)))
in ((uu____3414), (e2.FStar_Syntax_Syntax.pos)))
in (uu____3409)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____3402));
(

let uu____3425 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e2), (uu____3425)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____3427 = (

let uu____3428 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____3428))
in ((e2), (uu____3427)))
end));
)
end))
in (match (uu____3363) with
| (e2, g) -> begin
(

let c = (

let uu____3438 = (

let uu____3439 = (

let uu____3440 = (

let uu____3441 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____3441)::[])
in (

let uu____3442 = (

let uu____3451 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3451)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____3440; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____3442; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____3439))
in (FStar_All.pipe_right uu____3438 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3471 = (comp_check_expected_typ env1 e3 c)
in (match (uu____3471) with
| (e4, c1, g') -> begin
(

let uu____3487 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e4), (c1), (uu____3487)))
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

let uu____3534 = (

let uu____3535 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____3535 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____3534 instantiate_both))
in ((

let uu____3551 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____3551) with
| true -> begin
(

let uu____3552 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3553 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____3552 uu____3553)))
end
| uu____3554 -> begin
()
end));
(

let isquote = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.quote_lid) -> begin
true
end
| uu____3557 -> begin
false
end)
in (

let uu____3558 = (tc_term (no_inst env2) head1)
in (match (uu____3558) with
| (head2, chead, g_head) -> begin
(

let uu____3574 = (

let uu____3581 = ((not (env2.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____3581) with
| true -> begin
(

let uu____3588 = (

let uu____3595 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____3595))
in (match (uu____3588) with
| (e1, c, g) -> begin
(

let c1 = (

let uu____3608 = (((FStar_TypeChecker_Env.should_verify env2) && (

let uu____3610 = (FStar_Syntax_Util.is_lcomp_partial_return c)
in (not (uu____3610)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____3608) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e1 c)
end
| uu____3611 -> begin
c
end))
in ((e1), (c1), (g)))
end))
end
| uu____3612 -> begin
(

let env3 = (match (isquote) with
| true -> begin
(no_inst env2)
end
| uu____3614 -> begin
env2
end)
in (

let uu____3615 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env3 head2 chead g_head args uu____3615)))
end))
in (match (uu____3574) with
| (e1, c, g) -> begin
((

let uu____3628 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____3628) with
| true -> begin
(

let uu____3629 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____3629))
end
| uu____3630 -> begin
()
end));
(

let uu____3631 = (comp_check_expected_typ env0 e1 c)
in (match (uu____3631) with
| (e2, c1, g') -> begin
(

let gimp = (

let uu____3648 = (

let uu____3649 = (FStar_Syntax_Subst.compress head2)
in uu____3649.FStar_Syntax_Syntax.n)
in (match (uu____3648) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____3653) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e2), (c1.FStar_Syntax_Syntax.res_typ), (head2.FStar_Syntax_Syntax.pos))
in (

let uu___101_3715 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___101_3715.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___101_3715.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___101_3715.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____3764 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (

let uu____3766 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g uu____3766))
in ((

let uu____3768 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____3768) with
| true -> begin
(

let uu____3769 = (FStar_Syntax_Print.term_to_string e2)
in (

let uu____3770 = (FStar_TypeChecker_Rel.guard_to_string env2 gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____3769 uu____3770)))
end
| uu____3771 -> begin
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

let uu____3810 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3810) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____3830 = (tc_term env12 e1)
in (match (uu____3830) with
| (e11, c1, g1) -> begin
(

let uu____3846 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3856 = (FStar_Syntax_Util.type_u ())
in (match (uu____3856) with
| (k, uu____3866) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env1 k)
in (

let uu____3868 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in ((uu____3868), (res_t))))
end))
end)
in (match (uu____3846) with
| (env_branches, res_t) -> begin
((

let uu____3878 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____3878) with
| true -> begin
(

let uu____3879 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____3879))
end
| uu____3880 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____3965 = (

let uu____3970 = (FStar_List.fold_right (fun uu____4016 uu____4017 -> (match (((uu____4016), (uu____4017))) with
| ((uu____4080, f, c, g), (caccum, gaccum)) -> begin
(

let uu____4140 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (uu____4140)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3970) with
| (cases, g) -> begin
(

let uu____4179 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____4179), (g)))
end))
in (match (uu____3965) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____4275 -> (match (uu____4275) with
| ((pat, wopt, br), uu____4303, lc, uu____4305) -> begin
(

let uu____4318 = (FStar_TypeChecker_Util.maybe_lift env1 br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (uu____4318)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____4373 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____4373) with
| true -> begin
(mk_match e11)
end
| uu____4376 -> begin
(

let e_match = (

let uu____4380 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____4380))
in (

let lb = (

let uu____4384 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = uu____4384; FStar_Syntax_Syntax.lbdef = e11})
in (

let e2 = (

let uu____4388 = (

let uu____4391 = (

let uu____4392 = (

let uu____4405 = (

let uu____4406 = (

let uu____4407 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____4407)::[])
in (FStar_Syntax_Subst.close uu____4406 e_match))
in ((((false), ((lb)::[]))), (uu____4405)))
in FStar_Syntax_Syntax.Tm_let (uu____4392))
in (FStar_Syntax_Syntax.mk uu____4391))
in (uu____4388 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____4420 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____4420) with
| true -> begin
(

let uu____4421 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____4422 = (

let uu____4423 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____4423))
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____4421 uu____4422)))
end
| uu____4424 -> begin
()
end));
(

let uu____4425 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e2), (cres), (uu____4425)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4428); FStar_Syntax_Syntax.lbunivs = uu____4429; FStar_Syntax_Syntax.lbtyp = uu____4430; FStar_Syntax_Syntax.lbeff = uu____4431; FStar_Syntax_Syntax.lbdef = uu____4432})::[]), uu____4433) -> begin
((

let uu____4453 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____4453) with
| true -> begin
(

let uu____4454 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____4454))
end
| uu____4455 -> begin
()
end));
(check_top_level_let env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____4456), uu____4457) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4472); FStar_Syntax_Syntax.lbunivs = uu____4473; FStar_Syntax_Syntax.lbtyp = uu____4474; FStar_Syntax_Syntax.lbeff = uu____4475; FStar_Syntax_Syntax.lbdef = uu____4476})::uu____4477), uu____4478) -> begin
((

let uu____4500 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____4500) with
| true -> begin
(

let uu____4501 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____4501))
end
| uu____4502 -> begin
()
end));
(check_top_level_let_rec env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____4503), uu____4504) -> begin
(check_inner_let_rec env1 top)
end));
)))
and tc_synth : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env args rng -> (

let uu____4530 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.None), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4620))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.Some (a)), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4680))))::((uu____4681, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4682))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.Some (a)), (rest))
end
| uu____4755 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("synth_by_tactic: bad application"), (rng)))))
end)
in (match (uu____4530) with
| (tau, atyp, rest) -> begin
(

let typ = (match (atyp) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4839 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____4839) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4845 = (

let uu____4846 = (

let uu____4851 = (FStar_TypeChecker_Env.get_range env)
in (("synth_by_tactic: need a type annotation when no expected type is present"), (uu____4851)))
in FStar_Errors.Error (uu____4846))
in (FStar_Exn.raise uu____4845))
end))
end)
in (

let uu____4854 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____4854) with
| (env', uu____4868) -> begin
(

let uu____4873 = (tc_term env' typ)
in (match (uu____4873) with
| (typ1, uu____4887, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g1);
(

let uu____4890 = (tc_tactic env' tau)
in (match (uu____4890) with
| (tau1, uu____4904, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g2);
(

let uu____4908 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____4908) with
| true -> begin
(

let uu____4909 = (FStar_Syntax_Print.term_to_string tau1)
in (

let uu____4910 = (FStar_Syntax_Print.term_to_string typ1)
in (FStar_Util.print2 "Running tactic %s at return type %s\n" uu____4909 uu____4910)))
end
| uu____4911 -> begin
()
end));
(

let t = (env.FStar_TypeChecker_Env.synth env' typ1 tau1)
in ((

let uu____4914 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____4914) with
| true -> begin
(

let uu____4915 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____4915))
end
| uu____4916 -> begin
()
end));
(FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(

let uu____4918 = (FStar_Syntax_Syntax.mk_Tm_app t rest FStar_Pervasives_Native.None rng)
in (tc_term env uu____4918));
));
)
end));
)
end))
end)))
end)))
and tc_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___102_4922 = env
in {FStar_TypeChecker_Env.solver = uu___102_4922.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___102_4922.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___102_4922.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___102_4922.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___102_4922.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___102_4922.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___102_4922.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___102_4922.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___102_4922.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___102_4922.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___102_4922.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___102_4922.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___102_4922.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___102_4922.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___102_4922.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___102_4922.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___102_4922.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___102_4922.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___102_4922.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___102_4922.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.type_of = uu___102_4922.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___102_4922.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___102_4922.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___102_4922.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___102_4922.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___102_4922.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___102_4922.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___102_4922.FStar_TypeChecker_Env.identifier_info})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit)))
and tc_reified_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___103_4926 = env
in {FStar_TypeChecker_Env.solver = uu___103_4926.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___103_4926.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___103_4926.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___103_4926.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___103_4926.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___103_4926.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___103_4926.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___103_4926.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___103_4926.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___103_4926.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___103_4926.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___103_4926.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___103_4926.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___103_4926.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___103_4926.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___103_4926.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___103_4926.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___103_4926.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___103_4926.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___103_4926.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.type_of = uu___103_4926.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___103_4926.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___103_4926.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___103_4926.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___103_4926.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___103_4926.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___103_4926.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___103_4926.FStar_TypeChecker_Env.identifier_info})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____4942 = (tc_tactic env tactic)
in (match (uu____4942) with
| (tactic1, uu____4952, uu____4953) -> begin
FStar_Pervasives_Native.Some (tactic1)
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t -> (

let uu____4992 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____4992) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____5013 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5013) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____5018 -> begin
(

let uu____5019 = (

let uu____5020 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5020))
in FStar_Util.Inr (uu____5019))
end))
in (

let is_data_ctor = (fun uu___90_5030 -> (match (uu___90_5030) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5033)) -> begin
true
end
| uu____5040 -> begin
false
end))
in (

let uu____5043 = ((is_data_ctor dc) && (

let uu____5045 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____5045))))
in (match (uu____5043) with
| true -> begin
(

let uu____5052 = (

let uu____5053 = (

let uu____5058 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____5059 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____5058), (uu____5059))))
in FStar_Errors.Error (uu____5053))
in (FStar_Exn.raise uu____5052))
end
| uu____5066 -> begin
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

let uu____5076 = (

let uu____5077 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____5077))
in (failwith uu____5076))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____5111 = (

let uu____5112 = (FStar_Syntax_Subst.compress t1)
in uu____5112.FStar_Syntax_Syntax.n)
in (match (uu____5111) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5115) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____5128 -> begin
(

let imp = (("uvar in term"), (env1), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___104_5166 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___104_5166.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___104_5166.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___104_5166.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env1 e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____5218 = (

let uu____5231 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____5231) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5246 = (FStar_Syntax_Util.type_u ())
in (match (uu____5246) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____5218) with
| (t, uu____5283, g0) -> begin
(

let uu____5297 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____5297) with
| (e1, uu____5317, g1) -> begin
(

let uu____5331 = (

let uu____5332 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____5332 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____5333 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e1), (uu____5331), (uu____5333))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____5335 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____5348 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____5348)))
end
| uu____5351 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____5335) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___105_5367 = x
in {FStar_Syntax_Syntax.ppname = uu___105_5367.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___105_5367.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Env.insert_bv_info env1 x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____5370 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____5370) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____5391 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5391) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____5396 -> begin
(

let uu____5397 = (

let uu____5398 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5398))
in FStar_Util.Inr (uu____5397))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5404; FStar_Syntax_Syntax.vars = uu____5405}, uu____5406) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____5411 = (

let uu____5412 = (

let uu____5417 = (FStar_TypeChecker_Env.get_range env1)
in (("Badly instantiated synth_by_tactic"), (uu____5417)))
in FStar_Errors.Error (uu____5412))
in (FStar_Exn.raise uu____5411))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____5425 = (

let uu____5426 = (

let uu____5431 = (FStar_TypeChecker_Env.get_range env1)
in (("Badly instantiated synth_by_tactic"), (uu____5431)))
in FStar_Errors.Error (uu____5426))
in (FStar_Exn.raise uu____5425))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5439; FStar_Syntax_Syntax.vars = uu____5440}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____5449 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5449) with
| ((us', t), range) -> begin
((match (((FStar_List.length us1) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____5472 = (

let uu____5473 = (

let uu____5478 = (

let uu____5479 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____5480 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____5481 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____5479 uu____5480 uu____5481))))
in (

let uu____5482 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____5478), (uu____5482))))
in FStar_Errors.Error (uu____5473))
in (FStar_Exn.raise uu____5472))
end
| uu____5483 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____5498 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____5502 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5502 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5504 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5504) with
| ((us, t), range) -> begin
((

let uu____5527 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____5527) with
| true -> begin
(

let uu____5528 = (

let uu____5529 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____5529))
in (

let uu____5530 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____5531 = (FStar_Range.string_of_range range)
in (

let uu____5532 = (FStar_Range.string_of_use_range range)
in (

let uu____5533 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____5528 uu____5530 uu____5531 uu____5532 uu____5533))))))
end
| uu____5534 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____5538 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5538 us))
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

let uu____5562 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____5562) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____5576 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5576) with
| (env2, uu____5590) -> begin
(

let uu____5595 = (tc_binders env2 bs1)
in (match (uu____5595) with
| (bs2, env3, g, us) -> begin
(

let uu____5614 = (tc_comp env3 c1)
in (match (uu____5614) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___106_5633 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___106_5633.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___106_5633.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____5642 = (FStar_TypeChecker_Rel.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Rel.conj_guard g uu____5642))
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

let uu____5661 = (

let uu____5666 = (

let uu____5667 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5667)::[])
in (FStar_Syntax_Subst.open_term uu____5666 phi))
in (match (uu____5661) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____5677 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5677) with
| (env2, uu____5691) -> begin
(

let uu____5696 = (

let uu____5709 = (FStar_List.hd x1)
in (tc_binder env2 uu____5709))
in (match (uu____5696) with
| (x2, env3, f1, u) -> begin
((

let uu____5737 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____5737) with
| true -> begin
(

let uu____5738 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____5739 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____5740 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____5738 uu____5739 uu____5740))))
end
| uu____5741 -> begin
()
end));
(

let uu____5742 = (FStar_Syntax_Util.type_u ())
in (match (uu____5742) with
| (t_phi, uu____5754) -> begin
(

let uu____5755 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____5755) with
| (phi2, uu____5769, f2) -> begin
(

let e1 = (

let uu___107_5774 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___107_5774.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___107_5774.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____5781 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____5781))
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____5794) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____5817 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____5817) with
| true -> begin
(

let uu____5818 = (FStar_Syntax_Print.term_to_string (

let uu___108_5821 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.pos = uu___108_5821.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___108_5821.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____5818))
end
| uu____5826 -> begin
()
end));
(

let uu____5827 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____5827) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____5840 -> begin
(

let uu____5841 = (

let uu____5842 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____5843 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____5842 uu____5843)))
in (failwith uu____5841))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Syntax_Syntax.t_unit
end
| FStar_Const.Const_bool (uu____5852) -> begin
FStar_Syntax_Util.t_bool
end
| FStar_Const.Const_int (uu____5853, FStar_Pervasives_Native.None) -> begin
FStar_Syntax_Syntax.t_int
end
| FStar_Const.Const_int (uu____5864, FStar_Pervasives_Native.Some (uu____5865)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____5880) -> begin
FStar_Syntax_Syntax.t_string
end
| FStar_Const.Const_float (uu____5887) -> begin
FStar_Syntax_Syntax.t_float
end
| FStar_Const.Const_char (uu____5888) -> begin
FStar_Syntax_Syntax.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____5889) -> begin
FStar_Syntax_Syntax.t_range
end
| uu____5890 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____5907) -> begin
(

let uu____5916 = (FStar_Syntax_Util.type_u ())
in (match (uu____5916) with
| (k, u) -> begin
(

let uu____5929 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____5929) with
| (t1, uu____5943, g) -> begin
(

let uu____5945 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____5945), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____5947) -> begin
(

let uu____5956 = (FStar_Syntax_Util.type_u ())
in (match (uu____5956) with
| (k, u) -> begin
(

let uu____5969 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____5969) with
| (t1, uu____5983, g) -> begin
(

let uu____5985 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____5985), (u), (g)))
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

let uu____5993 = (

let uu____5994 = (

let uu____5995 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____5995)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____5994))
in (uu____5993 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____5998 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____5998) with
| (tc1, uu____6012, f) -> begin
(

let uu____6014 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____6014) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____6058 = (

let uu____6059 = (FStar_Syntax_Subst.compress head3)
in uu____6059.FStar_Syntax_Syntax.n)
in (match (uu____6058) with
| FStar_Syntax_Syntax.Tm_uinst (uu____6062, us) -> begin
us
end
| uu____6068 -> begin
[]
end))
in (

let uu____6069 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____6069) with
| (uu____6090, args1) -> begin
(

let uu____6112 = (

let uu____6131 = (FStar_List.hd args1)
in (

let uu____6144 = (FStar_List.tl args1)
in ((uu____6131), (uu____6144))))
in (match (uu____6112) with
| (res, args2) -> begin
(

let uu____6209 = (

let uu____6218 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___91_6246 -> (match (uu___91_6246) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____6254 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____6254) with
| (env1, uu____6266) -> begin
(

let uu____6271 = (tc_tot_or_gtot_term env1 e)
in (match (uu____6271) with
| (e1, uu____6283, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____6218 FStar_List.unzip))
in (match (uu____6209) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___109_6322 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___109_6322.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___109_6322.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____6326 = (FStar_TypeChecker_Env.effect_repr env c2 u)
in (match (uu____6326) with
| FStar_Pervasives_Native.None -> begin
u
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____6330 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c2), (u_c), (uu____6330))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____6338) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____6339) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____6349 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____6349))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____6353 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____6353))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u2
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____6357 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____6358 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6358 FStar_Pervasives_Native.snd))
end
| uu____6367 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (

let uu____6391 = (

let uu____6392 = (

let uu____6397 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((uu____6397), (top.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____6392))
in (FStar_Exn.raise uu____6391)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____6487 bs2 bs_expected1 -> (match (uu____6487) with
| (env2, out, g, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.None), (g), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((match (((imp), (imp'))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6655))) -> begin
(

let uu____6660 = (

let uu____6661 = (

let uu____6666 = (

let uu____6667 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____6667))
in (

let uu____6668 = (FStar_Syntax_Syntax.range_of_bv hd1)
in ((uu____6666), (uu____6668))))
in FStar_Errors.Error (uu____6661))
in (FStar_Exn.raise uu____6660))
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6669)), FStar_Pervasives_Native.None) -> begin
(

let uu____6674 = (

let uu____6675 = (

let uu____6680 = (

let uu____6681 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____6681))
in (

let uu____6682 = (FStar_Syntax_Syntax.range_of_bv hd1)
in ((uu____6680), (uu____6682))))
in FStar_Errors.Error (uu____6675))
in (FStar_Exn.raise uu____6674))
end
| uu____6683 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____6689 = (

let uu____6694 = (

let uu____6695 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____6695.FStar_Syntax_Syntax.n)
in (match (uu____6694) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____6702 -> begin
((

let uu____6704 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____6704) with
| true -> begin
(

let uu____6705 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____6705))
end
| uu____6706 -> begin
()
end));
(

let uu____6707 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____6707) with
| (t, uu____6719, g1) -> begin
(

let g2 = (

let uu____6722 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____6723 = (FStar_TypeChecker_Rel.teq env2 t expected_t)
in (FStar_TypeChecker_Util.label_guard uu____6722 "Type annotation on parameter incompatible with the expected type" uu____6723)))
in (

let g3 = (

let uu____6725 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____6725))
in ((t), (g3))))
end));
)
end))
in (match (uu____6689) with
| (t, g1) -> begin
(

let hd2 = (

let uu___110_6753 = hd1
in {FStar_Syntax_Syntax.ppname = uu___110_6753.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_6753.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env3 = (push_binding env2 b)
in (

let subst2 = (

let uu____6766 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____6766))
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
| uu____6920 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____6927 = (tc_binders env1 bs)
in (match (uu____6927) with
| (bs1, envbody, g, uu____6961) -> begin
(

let uu____6962 = (

let uu____6975 = (

let uu____6976 = (FStar_Syntax_Subst.compress body1)
in uu____6976.FStar_Syntax_Syntax.n)
in (match (uu____6975) with
| FStar_Syntax_Syntax.Tm_ascribed (e, (FStar_Util.Inr (c), tacopt), uu____6994) -> begin
(

let uu____7041 = (tc_comp envbody c)
in (match (uu____7041) with
| (c1, uu____7061, g') -> begin
(

let uu____7063 = (tc_tactic_opt envbody tacopt)
in (

let uu____7066 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((FStar_Pervasives_Native.Some (c1)), (uu____7063), (body1), (uu____7066))))
end))
end
| uu____7071 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (body1), (g))
end))
in (match (uu____6962) with
| (copt, tacopt, body2, g1) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (copt), (tacopt), (envbody), (body2), (g1))
end))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____7159 = (

let uu____7160 = (FStar_Syntax_Subst.compress t2)
in uu____7160.FStar_Syntax_Syntax.n)
in (match (uu____7159) with
| FStar_Syntax_Syntax.Tm_uvar (uu____7187) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____7209 -> begin
(failwith "Impossible")
end);
(

let uu____7216 = (tc_binders env1 bs)
in (match (uu____7216) with
| (bs1, envbody, g, uu____7252) -> begin
(

let uu____7253 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____7253) with
| (envbody1, uu____7285) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____7298); FStar_Syntax_Syntax.pos = uu____7299; FStar_Syntax_Syntax.vars = uu____7300}, uu____7301) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____7343 -> begin
(failwith "Impossible")
end);
(

let uu____7350 = (tc_binders env1 bs)
in (match (uu____7350) with
| (bs1, envbody, g, uu____7386) -> begin
(

let uu____7387 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____7387) with
| (envbody1, uu____7419) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____7433) -> begin
(

let uu____7438 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____7438) with
| (uu____7487, bs1, bs', copt, tacopt, env2, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), (bs'), (copt), (tacopt), (env2), (body2), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____7537 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____7537) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 -> (

let rec handle_more = (fun uu____7641 c_expected2 -> (match (uu____7641) with
| (env3, bs2, more, guard, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7756 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env3), (bs2), (guard), (uu____7756)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____7787 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____7787))
in (

let uu____7788 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env3), (bs2), (guard), (uu____7788))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (match ((FStar_Syntax_Util.is_named_tot c)) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env3 (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____7860 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____7860) with
| (bs_expected4, c_expected4) -> begin
(

let uu____7881 = (check_binders env3 more_bs bs_expected4)
in (match (uu____7881) with
| (env4, bs', more1, guard', subst2) -> begin
(

let uu____7929 = (

let uu____7960 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env4), ((FStar_List.append bs2 bs')), (more1), (uu____7960), (subst2)))
in (handle_more uu____7929 c_expected4))
end))
end))
end
| uu____7977 -> begin
(

let uu____7978 = (

let uu____7979 = (FStar_Syntax_Print.term_to_string t3)
in (FStar_Util.format1 "More arguments than annotated type (%s)" uu____7979))
in (fail uu____7978 t3))
end))
end
| uu____7994 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t2)
end))
end)
end))
in (

let uu____8009 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____8009 c_expected1))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___111_8068 = envbody
in {FStar_TypeChecker_Env.solver = uu___111_8068.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_8068.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_8068.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_8068.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_8068.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_8068.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_8068.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_8068.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_8068.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_8068.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_8068.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_8068.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___111_8068.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___111_8068.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_8068.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_8068.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_8068.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___111_8068.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___111_8068.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___111_8068.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___111_8068.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_8068.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_8068.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_8068.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___111_8068.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___111_8068.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___111_8068.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___111_8068.FStar_TypeChecker_Env.identifier_info})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____8107 uu____8108 -> (match (((uu____8107), (uu____8108))) with
| ((env2, letrec_binders), (l, t3)) -> begin
(

let uu____8153 = (

let uu____8160 = (

let uu____8161 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____8161 FStar_Pervasives_Native.fst))
in (tc_term uu____8160 t3))
in (match (uu____8153) with
| (t4, uu____8183, uu____8184) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l (([]), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____8194 = (FStar_Syntax_Syntax.mk_binder (

let uu___112_8197 = x
in {FStar_Syntax_Syntax.ppname = uu___112_8197.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_8197.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____8194)::letrec_binders)
end
| uu____8198 -> begin
letrec_binders
end)
in ((env3), (lb))))
end))
end)) ((envbody1), ([])))))))
in (

let uu____8203 = (check_actuals_against_formals env1 bs bs_expected1)
in (match (uu____8203) with
| (envbody, bs1, g, c) -> begin
(

let uu____8258 = (

let uu____8265 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____8265) with
| true -> begin
(mk_letrec_env envbody bs1 c)
end
| uu____8272 -> begin
((envbody), ([]))
end))
in (match (uu____8258) with
| (envbody1, letrecs) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in ((FStar_Pervasives_Native.Some (t2)), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (FStar_Pervasives_Native.None), (envbody2), (body1), (g)))
end))
end))))
end))
end
| uu____8320 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____8345 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____8345))
end
| uu____8346 -> begin
(

let uu____8347 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____8347) with
| (uu____8394, bs1, uu____8396, c_opt, tacopt, envbody, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (c_opt), (tacopt), (envbody), (body2), (g))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____8423 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8423) with
| (env1, topt) -> begin
((

let uu____8443 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____8443) with
| true -> begin
(

let uu____8444 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____8444 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____8446 -> begin
"false"
end)))
end
| uu____8447 -> begin
()
end));
(

let uu____8448 = (expected_function_typ1 env1 topt body)
in (match (uu____8448) with
| (tfun_opt, bs1, letrec_binders, c_opt, tacopt, envbody, body1, g) -> begin
(

let uu____8497 = (tc_term (

let uu___113_8506 = envbody
in {FStar_TypeChecker_Env.solver = uu___113_8506.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___113_8506.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___113_8506.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___113_8506.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___113_8506.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___113_8506.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___113_8506.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___113_8506.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___113_8506.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___113_8506.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___113_8506.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___113_8506.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___113_8506.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___113_8506.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___113_8506.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___113_8506.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___113_8506.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___113_8506.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___113_8506.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___113_8506.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___113_8506.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___113_8506.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___113_8506.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___113_8506.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___113_8506.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___113_8506.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___113_8506.FStar_TypeChecker_Env.identifier_info}) body1)
in (match (uu____8497) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in ((

let uu____8518 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Implicits")))
in (match (uu____8518) with
| true -> begin
(

let uu____8519 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body1.FStar_TypeChecker_Env.implicits))
in (

let uu____8532 = (

let uu____8533 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____8533))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" uu____8519 uu____8532)))
end
| uu____8534 -> begin
()
end));
(

let uu____8535 = (

let uu____8542 = (

let uu____8547 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body2), (uu____8547)))
in (check_expected_effect (

let uu___114_8554 = envbody
in {FStar_TypeChecker_Env.solver = uu___114_8554.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_8554.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_8554.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_8554.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_8554.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_8554.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_8554.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_8554.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_8554.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_8554.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_8554.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_8554.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_8554.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_8554.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_8554.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___114_8554.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_8554.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___114_8554.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_8554.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___114_8554.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___114_8554.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_8554.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_8554.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_8554.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___114_8554.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___114_8554.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___114_8554.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___114_8554.FStar_TypeChecker_Env.identifier_info}) c_opt uu____8542))
in (match (uu____8535) with
| (body3, cbody1, guard) -> begin
(

let guard1 = (FStar_TypeChecker_Rel.conj_guard guard_body1 guard)
in (

let guard2 = (

let uu____8566 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____8568 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____8568))))
in (match (uu____8566) with
| true -> begin
(

let uu____8569 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____8569))
end
| uu____8570 -> begin
(

let guard2 = (

let uu____8572 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in (FStar_TypeChecker_Rel.close_guard env1 (FStar_List.append bs1 letrec_binders) uu____8572))
in guard2)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody1)
in (

let e = (FStar_Syntax_Util.abs bs1 body3 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody1 c_opt)))))
in (

let uu____8581 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____8602) -> begin
((e), (t1), (guard2))
end
| uu____8615 -> begin
(

let uu____8616 = (FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
in (match (uu____8616) with
| (e1, guard') -> begin
(

let uu____8629 = (FStar_TypeChecker_Rel.conj_guard guard2 guard')
in ((e1), (t1), (uu____8629)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard2))
end)
in (match (uu____8581) with
| (e1, tfun, guard3) -> begin
(

let c = (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____8642 -> begin
(FStar_TypeChecker_Util.return_value env1 tfun e1)
end)
in (

let uu____8643 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 (FStar_Syntax_Util.lcomp_of_comp c) guard3)
in (match (uu____8643) with
| (c1, g1) -> begin
((e1), (c1), (g1))
end)))
end))))))
end));
))
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

let uu____8692 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8692) with
| true -> begin
(

let uu____8693 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____8694 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____8693 uu____8694)))
end
| uu____8695 -> begin
()
end));
(

let monadic_application = (fun uu____8751 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____8751) with
| (head2, chead1, ghead1, cres) -> begin
(

let rt = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres1 = (

let uu___115_8810 = cres
in {FStar_Syntax_Syntax.eff_name = uu___115_8810.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___115_8810.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___115_8810.FStar_Syntax_Syntax.comp})
in (

let uu____8811 = (match (bs) with
| [] -> begin
(

let cres2 = (FStar_TypeChecker_Util.subst_lcomp subst1 cres1)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in ((cres2), (g))))
end
| uu____8826 -> begin
(

let g = (

let uu____8834 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____8834 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (

let uu____8835 = (

let uu____8836 = (

let uu____8839 = (

let uu____8840 = (

let uu____8841 = (cres1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs uu____8841))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst1) uu____8840))
in (FStar_Syntax_Syntax.mk_Total uu____8839))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8836))
in ((uu____8835), (g))))
end)
in (match (uu____8811) with
| (cres2, guard1) -> begin
((

let uu____8855 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____8855) with
| true -> begin
(

let uu____8856 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____8856))
end
| uu____8857 -> begin
()
end));
(

let cres3 = (

let uu____8859 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2)
in (match (uu____8859) with
| true -> begin
(

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2))
end
| uu____8869 -> begin
cres2
end))
in (

let comp = (FStar_List.fold_left (fun out_c uu____8893 -> (match (uu____8893) with
| ((e, q), x, c) -> begin
(

let uu____8926 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____8926) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____8931 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end))
end)) cres3 arg_comps_rev)
in (

let comp1 = (FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
in (

let shortcuts_evaluation_order = (

let uu____8938 = (

let uu____8939 = (FStar_Syntax_Subst.compress head2)
in uu____8939.FStar_Syntax_Syntax.n)
in (match (uu____8938) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____8943 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____8964 -> (match (uu____8964) with
| (arg, uu____8978, uu____8979) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ))))
end
| uu____8988 -> begin
(

let uu____8989 = (

let map_fun = (fun uu____9051 -> (match (uu____9051) with
| ((e, q), uu____9086, c) -> begin
(

let uu____9096 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____9096) with
| true -> begin
((FStar_Pervasives_Native.None), (((e), (q))))
end
| uu____9143 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____9146 = (

let uu____9151 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____9151), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____9146)))))
end))
end))
in (

let uu____9180 = (

let uu____9205 = (

let uu____9228 = (

let uu____9243 = (

let uu____9252 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____9252), (FStar_Pervasives_Native.None), (chead1)))
in (uu____9243)::arg_comps_rev)
in (FStar_List.map map_fun uu____9228))
in (FStar_All.pipe_left FStar_List.split uu____9205))
in (match (uu____9180) with
| (lifted_args, reverse_args) -> begin
(

let uu____9425 = (

let uu____9426 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____9426))
in (

let uu____9435 = (

let uu____9442 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____9442))
in ((lifted_args), (uu____9425), (uu____9435))))
end)))
in (match (uu____8989) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___92_9545 -> (match (uu___92_9545) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1)
in (

let letbinding = (

let uu____9600 = (

let uu____9603 = (

let uu____9604 = (

let uu____9617 = (

let uu____9618 = (

let uu____9619 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____9619)::[])
in (FStar_Syntax_Subst.close uu____9618 e))
in ((((false), ((lb)::[]))), (uu____9617)))
in FStar_Syntax_Syntax.Tm_let (uu____9604))
in (FStar_Syntax_Syntax.mk uu____9603))
in (uu____9600 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp1.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____9649 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp1 guard1)
in (match (uu____9649) with
| (comp2, g) -> begin
((app), (comp2), (g))
end)))))));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____9740 bs args1 -> (match (uu____9740) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9887))))::rest, ((uu____9889, FStar_Pervasives_Native.None))::uu____9890) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let t1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (

let uu____9951 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____9951) with
| (varg, uu____9971, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____9993 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____9993)))
in (

let uu____9994 = (

let uu____10029 = (

let uu____10044 = (

let uu____10057 = (

let uu____10058 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____10058 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____10057)))
in (uu____10044)::outargs)
in (

let uu____10077 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst2), (uu____10029), ((arg)::arg_rets), (uu____10077), (fvs))))
in (tc_args head_info uu____9994 rest args1))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10179)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10180))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____10193 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___116_10204 = x
in {FStar_Syntax_Syntax.ppname = uu___116_10204.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_10204.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____10206 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10206) with
| true -> begin
(

let uu____10207 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____10207))
end
| uu____10208 -> begin
()
end));
(

let targ1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___117_10212 = env1
in {FStar_TypeChecker_Env.solver = uu___117_10212.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_10212.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_10212.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_10212.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_10212.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_10212.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_10212.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_10212.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_10212.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_10212.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_10212.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_10212.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_10212.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___117_10212.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___117_10212.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___117_10212.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_10212.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___117_10212.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___117_10212.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___117_10212.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___117_10212.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_10212.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___117_10212.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___117_10212.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___117_10212.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___117_10212.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___117_10212.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___117_10212.FStar_TypeChecker_Env.identifier_info})
in ((

let uu____10214 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____10214) with
| true -> begin
(

let uu____10215 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____10216 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____10217 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____10215 uu____10216 uu____10217))))
end
| uu____10218 -> begin
()
end));
(

let uu____10219 = (tc_term env2 e)
in (match (uu____10219) with
| (e1, c, g_e) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____10246 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____10246))
in (

let uu____10247 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____10247) with
| true -> begin
(

let subst2 = (

let uu____10255 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____10255 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____10304 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
))));
)));
)
end
| (uu____10349, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____10385) -> begin
(

let uu____10436 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____10436) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 tres -> (

let tres1 = (

let uu____10470 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____10470 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____10495 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____10495) with
| (bs2, cres'1) -> begin
(

let head_info1 = ((head2), (chead1), (ghead1), ((FStar_Syntax_Util.lcomp_of_comp cres'1)))
in ((

let uu____10518 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____10518) with
| true -> begin
(

let uu____10519 = (FStar_Range.string_of_range tres1.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" uu____10519))
end
| uu____10520 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____10561 when (not (norm1)) -> begin
(

let uu____10562 = (FStar_TypeChecker_Normalize.unfold_whnf env tres1)
in (aux true uu____10562))
end
| uu____10563 -> begin
(

let uu____10564 = (

let uu____10565 = (

let uu____10570 = (

let uu____10571 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____10572 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" uu____10571 uu____10572)))
in (

let uu____10579 = (FStar_Syntax_Syntax.argpos arg)
in ((uu____10570), (uu____10579))))
in FStar_Errors.Error (uu____10565))
in (FStar_Exn.raise uu____10564))
end)))
in (aux false chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf -> (

let uu____10598 = (

let uu____10599 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____10599.FStar_Syntax_Syntax.n)
in (match (uu____10598) with
| FStar_Syntax_Syntax.Tm_uvar (uu____10610) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____10711 = (tc_term env1 e)
in (match (uu____10711) with
| (e1, c, g_e) -> begin
(

let uu____10733 = (tc_args1 env1 tl1)
in (match (uu____10733) with
| (args2, comps, g_rest) -> begin
(

let uu____10773 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____10773)))
end))
end))
end))
in (

let uu____10794 = (tc_args1 env args)
in (match (uu____10794) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____10831 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____10869 -> (match (uu____10869) with
| (uu____10882, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____10831))
in (

let ml_or_tot = (fun t r1 -> (

let uu____10899 = (FStar_Options.ml_ish ())
in (match (uu____10899) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____10900 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____10902 = (

let uu____10905 = (

let uu____10906 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____10906 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____10905))
in (ml_or_tot uu____10902 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____10919 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____10919) with
| true -> begin
(

let uu____10920 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____10921 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____10922 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____10920 uu____10921 uu____10922))))
end
| uu____10923 -> begin
()
end));
(

let uu____10925 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____10925));
(

let comp = (

let uu____10927 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____10938 out -> (match (uu____10938) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____10927))
in (

let uu____10952 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let uu____10955 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____10952), (comp), (uu____10955)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____10958); FStar_Syntax_Syntax.pos = uu____10959; FStar_Syntax_Syntax.vars = uu____10960}, uu____10961) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____11082 = (tc_term env1 e)
in (match (uu____11082) with
| (e1, c, g_e) -> begin
(

let uu____11104 = (tc_args1 env1 tl1)
in (match (uu____11104) with
| (args2, comps, g_rest) -> begin
(

let uu____11144 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____11144)))
end))
end))
end))
in (

let uu____11165 = (tc_args1 env args)
in (match (uu____11165) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____11202 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____11240 -> (match (uu____11240) with
| (uu____11253, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____11202))
in (

let ml_or_tot = (fun t r1 -> (

let uu____11270 = (FStar_Options.ml_ish ())
in (match (uu____11270) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____11271 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____11273 = (

let uu____11276 = (

let uu____11277 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____11277 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____11276))
in (ml_or_tot uu____11273 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____11290 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____11290) with
| true -> begin
(

let uu____11291 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____11292 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____11293 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____11291 uu____11292 uu____11293))))
end
| uu____11294 -> begin
()
end));
(

let uu____11296 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____11296));
(

let comp = (

let uu____11298 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____11309 out -> (match (uu____11309) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____11298))
in (

let uu____11323 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let uu____11326 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____11323), (comp), (uu____11326)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____11347 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____11347) with
| (bs1, c1) -> begin
(

let head_info = ((head1), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c1)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs1 args))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____11412) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____11418, uu____11419) -> begin
(check_function_app t)
end
| uu____11460 -> begin
(

let uu____11461 = (

let uu____11462 = (

let uu____11467 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((uu____11467), (head1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____11462))
in (FStar_Exn.raise uu____11461))
end)))
in (check_function_app thead))));
)))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head1 chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let uu____11537 = (FStar_List.fold_left2 (fun uu____11580 uu____11581 uu____11582 -> (match (((uu____11580), (uu____11581), (uu____11582))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((aq <> aq')) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____11649 -> begin
()
end);
(

let uu____11650 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____11650) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____11668 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____11668 g))
in (

let ghost1 = (ghost || ((

let uu____11672 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____11672))) && (

let uu____11674 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____11674)))))
in (

let uu____11675 = (

let uu____11684 = (

let uu____11693 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____11693)::[])
in (FStar_List.append seen uu____11684))
in (

let uu____11700 = (FStar_TypeChecker_Rel.conj_guard guard g1)
in ((uu____11675), (uu____11700), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____11537) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____11736 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____11736 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____11737 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____11738 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____11738) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____11755 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____11789 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____11789) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____11825 = branch1
in (match (uu____11825) with
| (cpat, uu____11857, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let uu____11909 = (FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0)
in (match (uu____11909) with
| (pat_bvs1, exp, p) -> begin
((

let uu____11938 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____11938) with
| true -> begin
(

let uu____11939 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____11940 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____11939 uu____11940)))
end
| uu____11941 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs1)
in (

let uu____11943 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____11943) with
| (env1, uu____11963) -> begin
(

let env11 = (

let uu___118_11969 = env1
in {FStar_TypeChecker_Env.solver = uu___118_11969.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___118_11969.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___118_11969.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___118_11969.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___118_11969.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___118_11969.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___118_11969.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___118_11969.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___118_11969.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___118_11969.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___118_11969.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___118_11969.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___118_11969.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___118_11969.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___118_11969.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___118_11969.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___118_11969.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___118_11969.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___118_11969.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___118_11969.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___118_11969.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___118_11969.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___118_11969.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___118_11969.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___118_11969.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___118_11969.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___118_11969.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___118_11969.FStar_TypeChecker_Env.identifier_info})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in ((

let uu____11972 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____11972) with
| true -> begin
(

let uu____11973 = (FStar_Syntax_Print.term_to_string exp)
in (

let uu____11974 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____11973 uu____11974)))
end
| uu____11975 -> begin
()
end));
(

let env12 = (FStar_TypeChecker_Env.set_expected_typ env11 expected_pat_t)
in (

let uu____11977 = (tc_tot_or_gtot_term env12 exp)
in (match (uu____11977) with
| (exp1, lc, g) -> begin
(

let g1 = (

let uu___119_12000 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___119_12000.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___119_12000.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___119_12000.FStar_TypeChecker_Env.implicits})
in (

let uu____12001 = (

let g' = (FStar_TypeChecker_Rel.teq env12 lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g2 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in (

let env13 = (FStar_TypeChecker_Env.set_range env12 exp1.FStar_Syntax_Syntax.pos)
in (

let uu____12005 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env13 g2)
in (FStar_All.pipe_right uu____12005 FStar_TypeChecker_Rel.resolve_implicits)))))
in (

let norm_exp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env12 exp1)
in (

let uvs1 = (FStar_Syntax_Free.uvars norm_exp)
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____12022 = (

let uu____12023 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____12023))
in (match (uu____12022) with
| true -> begin
(

let unresolved = (

let uu____12035 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right uu____12035 FStar_Util.set_elements))
in (

let uu____12062 = (

let uu____12063 = (

let uu____12068 = (

let uu____12069 = (FStar_TypeChecker_Normalize.term_to_string env norm_exp)
in (

let uu____12070 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____12071 = (

let uu____12072 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____12090 -> (match (uu____12090) with
| (u, uu____12096) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____12072 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____12069 uu____12070 uu____12071))))
in ((uu____12068), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____12063))
in (FStar_Exn.raise uu____12062)))
end
| uu____12099 -> begin
()
end));
(

let uu____12101 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____12101) with
| true -> begin
(

let uu____12102 = (FStar_TypeChecker_Normalize.term_to_string env exp1)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____12102))
end
| uu____12103 -> begin
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
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let uu____12111 = (

let uu____12118 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____12118 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____12111) with
| (scrutinee_env, uu____12142) -> begin
(

let uu____12147 = (tc_pat true pat_t pattern)
in (match (uu____12147) with
| (pattern1, pat_bvs1, pat_env, pat_exp, norm_pat_exp) -> begin
(

let uu____12185 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____12207 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____12207) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____12220 -> begin
(

let uu____12221 = (

let uu____12228 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_Syntax_Util.t_bool)
in (tc_term uu____12228 e))
in (match (uu____12221) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____12185) with
| (when_clause1, g_when) -> begin
(

let uu____12262 = (tc_term pat_env branch_exp)
in (match (uu____12262) with
| (branch_exp1, c, g_branch) -> begin
(

let when_condition = (match (when_clause1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____12294 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____12294))
end)
in (

let uu____12297 = (

let eqs = (

let uu____12307 = (

let uu____12308 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12308)))
in (match (uu____12307) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12311 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____12315) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____12332) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____12333) -> begin
FStar_Pervasives_Native.None
end
| uu____12334 -> begin
(

let uu____12335 = (

let uu____12336 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____12336 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____12335))
end))
end))
in (

let uu____12337 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch)
in (match (uu____12337) with
| (c1, g_branch1) -> begin
(

let uu____12352 = (match (((eqs), (when_condition))) with
| uu____12365 when (

let uu____12374 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12374))) -> begin
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

let uu____12386 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____12387 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____12386), (uu____12387))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____12396 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____12396))
in (

let uu____12397 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____12398 = (

let uu____12399 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____12399 g_when))
in ((uu____12397), (uu____12398))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____12407 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____12407), (g_when)))))
end)
in (match (uu____12352) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let uu____12419 = (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak)
in (

let uu____12420 = (FStar_TypeChecker_Rel.close_guard env binders g_when_weak)
in ((uu____12419), (uu____12420), (g_branch1)))))
end))
end)))
in (match (uu____12297) with
| (c1, g_when1, g_branch1) -> begin
(

let branch_guard = (

let uu____12441 = (

let uu____12442 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12442)))
in (match (uu____12441) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____12443 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____12472 = (

let uu____12473 = (

let uu____12474 = (

let uu____12477 = (

let uu____12484 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____12484))
in (FStar_Pervasives_Native.snd uu____12477))
in (FStar_List.length uu____12474))
in (uu____12473 > (Prims.parse_int "1")))
in (match (uu____12472) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____12490 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____12490) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____12511 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____12526 = (

let uu____12527 = (

let uu____12528 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____12528)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____12527))
in (uu____12526 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____12531 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____12531)::[])))
end)))
end
| uu____12532 -> begin
[]
end)))
in (

let fail = (fun uu____12536 -> (

let uu____12537 = (

let uu____12538 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____12539 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____12540 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____12538 uu____12539 uu____12540))))
in (failwith uu____12537)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____12551) -> begin
(head_constructor t1)
end
| uu____12556 -> begin
(fail ())
end))
in (

let pat_exp2 = (

let uu____12558 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____12558 FStar_Syntax_Util.unmeta))
in (match (pat_exp2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____12561) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12578); FStar_Syntax_Syntax.pos = uu____12579; FStar_Syntax_Syntax.vars = uu____12580}, uu____12581) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_name (uu____12618) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (c2) -> begin
(

let uu____12620 = (

let uu____12621 = (tc_constant pat_exp2.FStar_Syntax_Syntax.pos c2)
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____12621 scrutinee_tm1 pat_exp2))
in (uu____12620)::[])
end
| FStar_Syntax_Syntax.Tm_uinst (uu____12622) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____12630 = (

let uu____12631 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____12631)))
in (match (uu____12630) with
| true -> begin
[]
end
| uu____12634 -> begin
(

let uu____12635 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____12635))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____12638) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____12640 = (

let uu____12641 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____12641)))
in (match (uu____12640) with
| true -> begin
[]
end
| uu____12644 -> begin
(

let uu____12645 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____12645))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let f = (head_constructor head1)
in (

let uu____12671 = (

let uu____12672 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____12672)))
in (match (uu____12671) with
| true -> begin
[]
end
| uu____12675 -> begin
(

let sub_term_guards = (

let uu____12679 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____12711 -> (match (uu____12711) with
| (ei, uu____12721) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____12727 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____12727) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____12748 -> begin
(

let sub_term = (

let uu____12762 = (

let uu____12763 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____12764 = (

let uu____12765 = (FStar_Syntax_Syntax.as_arg scrutinee_tm1)
in (uu____12765)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____12763 uu____12764)))
in (uu____12762 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____12679 FStar_List.flatten))
in (

let uu____12774 = (discriminate scrutinee_tm1 f)
in (FStar_List.append uu____12774 sub_term_guards)))
end)))
end
| uu____12777 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pat -> (

let uu____12789 = (

let uu____12790 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12790)))
in (match (uu____12789) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____12791 -> begin
(

let t = (

let uu____12793 = (build_branch_guard scrutinee_tm1 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____12793))
in (

let uu____12798 = (FStar_Syntax_Util.type_u ())
in (match (uu____12798) with
| (k, uu____12804) -> begin
(

let uu____12805 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____12805) with
| (t1, uu____12813, uu____12814) -> begin
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

let uu____12820 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____12820) with
| true -> begin
(

let uu____12821 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____12821))
end
| uu____12822 -> begin
()
end));
(

let uu____12823 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in ((uu____12823), (branch_guard), (c1), (guard)));
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

let uu____12849 = (check_let_bound_def true env1 lb)
in (match (uu____12849) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____12871 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____12888 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____12888), (univ_vars1), (c1)))
end
| uu____12889 -> begin
(

let g11 = (

let uu____12891 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____12891 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____12895 = (

let uu____12904 = (

let uu____12915 = (

let uu____12924 = (

let uu____12937 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____12937)))
in (uu____12924)::[])
in (FStar_TypeChecker_Util.generalize env1 uu____12915))
in (FStar_List.hd uu____12904))
in (match (uu____12895) with
| (uu____12986, univs1, e11, c11) -> begin
((g11), (e11), (univs1), ((FStar_Syntax_Util.lcomp_of_comp c11)))
end)))
end)
in (match (uu____12871) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____13000 = (

let uu____13007 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____13007) with
| true -> begin
(

let uu____13014 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____13014) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____13035 -> begin
((

let uu____13037 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.warn uu____13037 FStar_TypeChecker_Err.top_level_effect));
(

let uu____13038 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____13038), (c12)));
)
end)
end))
end
| uu____13045 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____13048 = (c11.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right uu____13048 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env1)))
in (

let e21 = (

let uu____13056 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____13056) with
| true -> begin
e2
end
| uu____13059 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end))
in ((e21), (c))));
)
end))
in (match (uu____13000) with
| (e21, c12) -> begin
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit)
in (

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e11)
in (

let uu____13080 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in ((uu____13080), ((FStar_Syntax_Util.lcomp_of_comp cres)), (FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| uu____13095 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___120_13126 = env1
in {FStar_TypeChecker_Env.solver = uu___120_13126.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___120_13126.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___120_13126.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___120_13126.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___120_13126.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___120_13126.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___120_13126.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___120_13126.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___120_13126.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___120_13126.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___120_13126.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___120_13126.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___120_13126.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___120_13126.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___120_13126.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___120_13126.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___120_13126.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___120_13126.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___120_13126.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___120_13126.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___120_13126.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___120_13126.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___120_13126.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___120_13126.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___120_13126.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___120_13126.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___120_13126.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___120_13126.FStar_TypeChecker_Env.identifier_info})
in (

let uu____13127 = (

let uu____13138 = (

let uu____13139 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____13139 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____13138 lb))
in (match (uu____13127) with
| (e1, uu____13161, c1, g1, annotated) -> begin
(

let x = (

let uu___121_13166 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___121_13166.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_13166.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____13167 = (

let uu____13172 = (

let uu____13173 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____13173)::[])
in (FStar_Syntax_Subst.open_term uu____13172 e2))
in (match (uu____13167) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let uu____13192 = (

let uu____13199 = (FStar_TypeChecker_Env.push_bv env2 x1)
in (tc_term uu____13199 e21))
in (match (uu____13192) with
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

let uu____13218 = (

let uu____13221 = (

let uu____13222 = (

let uu____13235 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____13235)))
in FStar_Syntax_Syntax.Tm_let (uu____13222))
in (FStar_Syntax_Syntax.mk uu____13221))
in (uu____13218 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____13249 = (

let uu____13250 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____13251 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____13250 c1.FStar_Syntax_Syntax.res_typ uu____13251 e11)))
in (FStar_All.pipe_left (fun _0_43 -> FStar_TypeChecker_Common.NonTrivial (_0_43)) uu____13249))
in (

let g21 = (

let uu____13253 = (

let uu____13254 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____13254 g2))
in (FStar_TypeChecker_Rel.close_guard env2 xb uu____13253))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g21)
in (

let uu____13256 = (

let uu____13257 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____13257))
in (match (uu____13256) with
| true -> begin
(

let tt = (

let uu____13267 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____13267 FStar_Option.get))
in ((

let uu____13273 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____13273) with
| true -> begin
(

let uu____13274 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____13275 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____13274 uu____13275)))
end
| uu____13276 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____13277 -> begin
(

let t = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____13280 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____13280) with
| true -> begin
(

let uu____13281 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____13282 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____13281 uu____13282)))
end
| uu____13283 -> begin
()
end));
((e4), ((

let uu___122_13285 = cres
in {FStar_Syntax_Syntax.eff_name = uu___122_13285.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___122_13285.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___122_13285.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____13286 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____13318 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____13318) with
| (lbs1, e21) -> begin
(

let uu____13337 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____13337) with
| (env0, topt) -> begin
(

let uu____13356 = (build_let_rec_env true env0 lbs1)
in (match (uu____13356) with
| (lbs2, rec_env) -> begin
(

let uu____13375 = (check_let_recs rec_env lbs2)
in (match (uu____13375) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____13395 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g_lbs)
in (FStar_All.pipe_right uu____13395 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (

let uu____13401 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____13401 (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((lb.FStar_Syntax_Syntax.lbunivs = [])) with
| true -> begin
lb
end
| uu____13433 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef)
end)))))
end
| uu____13434 -> begin
(

let ecs = (

let uu____13446 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____13486 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____13486))))))
in (FStar_TypeChecker_Util.generalize env1 uu____13446))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____13526 -> (match (uu____13526) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (

let uu____13564 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____13564))
in (

let uu____13569 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____13569) with
| (lbs5, e22) -> begin
((

let uu____13589 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____13589 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____13590 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____13590), (cres), (FStar_TypeChecker_Rel.trivial_guard)));
)
end))))))
end))
end))
end))
end))
end
| uu____13603 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____13635 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____13635) with
| (lbs1, e21) -> begin
(

let uu____13654 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____13654) with
| (env0, topt) -> begin
(

let uu____13673 = (build_let_rec_env false env0 lbs1)
in (match (uu____13673) with
| (lbs2, rec_env) -> begin
(

let uu____13692 = (check_let_recs rec_env lbs2)
in (match (uu____13692) with
| (lbs3, g_lbs) -> begin
(

let uu____13711 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___123_13734 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___123_13734.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_13734.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___124_13736 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___124_13736.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___124_13736.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___124_13736.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___124_13736.FStar_Syntax_Syntax.lbdef})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____13711) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____13763 = (tc_term env2 e21)
in (match (uu____13763) with
| (e22, cres, g2) -> begin
(

let guard = (

let uu____13780 = (

let uu____13781 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Rel.close_guard env2 uu____13781 g2))
in (FStar_TypeChecker_Rel.conj_guard g_lbs uu____13780))
in (

let cres1 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres)
in (

let tres = (norm env2 cres1.FStar_Syntax_Syntax.res_typ)
in (

let cres2 = (

let uu___125_13785 = cres1
in {FStar_Syntax_Syntax.eff_name = uu___125_13785.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___125_13785.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___125_13785.FStar_Syntax_Syntax.comp})
in (

let uu____13786 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____13786) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____13822) -> begin
((e), (cres2), (guard))
end
| FStar_Pervasives_Native.None -> begin
(

let tres1 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (

let cres3 = (

let uu___126_13827 = cres2
in {FStar_Syntax_Syntax.eff_name = uu___126_13827.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___126_13827.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___126_13827.FStar_Syntax_Syntax.comp})
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
| uu____13830 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____13860 = (

let uu____13865 = (

let uu____13866 = (FStar_Syntax_Subst.compress t)
in uu____13866.FStar_Syntax_Syntax.n)
in (

let uu____13869 = (

let uu____13870 = (FStar_Syntax_Subst.compress lbdef)
in uu____13870.FStar_Syntax_Syntax.n)
in ((uu____13865), (uu____13869))))
in (match (uu____13860) with
| (FStar_Syntax_Syntax.Tm_arrow (formals, c), FStar_Syntax_Syntax.Tm_abs (actuals, uu____13876, uu____13877)) -> begin
(

let actuals1 = (

let uu____13915 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____13915 actuals))
in ((match (((FStar_List.length formals) <> (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((n1 = (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____13935 -> begin
(

let uu____13936 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____13936))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((n1 = (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____13953 -> begin
(

let uu____13954 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____13954))
end))
in (

let msg = (

let uu____13962 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____13963 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____13962 uu____13963 formals_msg actuals_msg)))
in (FStar_Exn.raise (FStar_Errors.Error (((msg), (lbdef.FStar_Syntax_Syntax.pos))))))))
end
| uu____13964 -> begin
()
end);
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)));
))
end
| uu____13970 -> begin
(

let uu____13975 = (

let uu____13976 = (

let uu____13981 = (

let uu____13982 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____13983 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____13982 uu____13983)))
in ((uu____13981), (lbtyp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____13976))
in (FStar_Exn.raise uu____13975))
end))))
in (

let uu____13984 = (FStar_List.fold_left (fun uu____14010 lb -> (match (uu____14010) with
| (lbs1, env1) -> begin
(

let uu____14030 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____14030) with
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
| uu____14049 -> begin
(

let uu____14050 = (

let uu____14057 = (

let uu____14058 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14058))
in (tc_check_tot_or_gtot_term (

let uu___127_14069 = env0
in {FStar_TypeChecker_Env.solver = uu___127_14069.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___127_14069.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___127_14069.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___127_14069.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___127_14069.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___127_14069.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___127_14069.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___127_14069.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___127_14069.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___127_14069.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___127_14069.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___127_14069.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___127_14069.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___127_14069.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___127_14069.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___127_14069.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___127_14069.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___127_14069.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___127_14069.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___127_14069.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___127_14069.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___127_14069.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___127_14069.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___127_14069.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___127_14069.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___127_14069.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___127_14069.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___127_14069.FStar_TypeChecker_Env.identifier_info}) t uu____14057))
in (match (uu____14050) with
| (t1, uu____14071, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((

let uu____14075 = (FStar_TypeChecker_Rel.discharge_guard env2 g1)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____14075));
(norm env0 t1);
))
end))
end)
in (

let env3 = (

let uu____14077 = ((termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1) && (FStar_TypeChecker_Env.should_verify env2))
in (match (uu____14077) with
| true -> begin
(

let uu___128_14078 = env2
in {FStar_TypeChecker_Env.solver = uu___128_14078.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___128_14078.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___128_14078.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___128_14078.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___128_14078.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___128_14078.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___128_14078.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___128_14078.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___128_14078.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___128_14078.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___128_14078.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___128_14078.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___128_14078.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___128_14078.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___128_14078.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___128_14078.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___128_14078.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___128_14078.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___128_14078.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___128_14078.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___128_14078.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___128_14078.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___128_14078.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___128_14078.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___128_14078.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___128_14078.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___128_14078.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___128_14078.FStar_TypeChecker_Env.identifier_info})
end
| uu____14091 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname (([]), (t1)))
end))
in (

let lb1 = (

let uu___129_14095 = lb
in {FStar_Syntax_Syntax.lbname = uu___129_14095.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___129_14095.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb1)::lbs1), (env3)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____13984) with
| (lbs1, env1) -> begin
(((FStar_List.rev lbs1)), (env1))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____14118 = (

let uu____14127 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> ((

let uu____14156 = (

let uu____14157 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____14157.FStar_Syntax_Syntax.n)
in (match (uu____14156) with
| FStar_Syntax_Syntax.Tm_abs (uu____14160) -> begin
()
end
| uu____14177 -> begin
(

let uu____14178 = (

let uu____14179 = (

let uu____14184 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (("Only function literals may be defined recursively"), (uu____14184)))
in FStar_Errors.Error (uu____14179))
in (FStar_Exn.raise uu____14178))
end));
(

let uu____14185 = (

let uu____14192 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____14192 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____14185) with
| (e, c, g) -> begin
((

let uu____14201 = (

let uu____14202 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____14202)))
in (match (uu____14201) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____14203 -> begin
()
end));
(

let lb1 = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e)
in ((lb1), (g)));
)
end));
))))
in (FStar_All.pipe_right uu____14127 FStar_List.unzip))
in (match (uu____14118) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____14251 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____14251) with
| (env1, uu____14269) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____14277 = (check_lbtyp top_level env lb)
in (match (uu____14277) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (univ_vars1 <> []))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____14316 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____14321 = (tc_maybe_toplevel_term (

let uu___130_14330 = env11
in {FStar_TypeChecker_Env.solver = uu___130_14330.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___130_14330.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___130_14330.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___130_14330.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___130_14330.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___130_14330.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___130_14330.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___130_14330.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___130_14330.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___130_14330.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___130_14330.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___130_14330.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___130_14330.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___130_14330.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___130_14330.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___130_14330.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___130_14330.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___130_14330.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___130_14330.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___130_14330.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___130_14330.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___130_14330.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___130_14330.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___130_14330.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___130_14330.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___130_14330.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___130_14330.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___130_14330.FStar_TypeChecker_Env.identifier_info}) e11)
in (match (uu____14321) with
| (e12, c1, g1) -> begin
(

let uu____14344 = (

let uu____14349 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____14353 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____14349 e12 c1 wf_annot))
in (match (uu____14344) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____14368 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14368) with
| true -> begin
(

let uu____14369 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____14370 = (FStar_Syntax_Print.term_to_string c11.FStar_Syntax_Syntax.res_typ)
in (

let uu____14371 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" uu____14369 uu____14370 uu____14371))))
end
| uu____14372 -> begin
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
((match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end
| uu____14408 -> begin
()
end);
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____14415 -> begin
(

let uu____14416 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____14416) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____14465 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____14465)))
end
| uu____14472 -> begin
(

let uu____14473 = (FStar_Syntax_Util.type_u ())
in (match (uu____14473) with
| (k, uu____14493) -> begin
(

let uu____14494 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____14494) with
| (t2, uu____14516, g) -> begin
((

let uu____14519 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____14519) with
| true -> begin
(

let uu____14520 = (

let uu____14521 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____14521))
in (

let uu____14522 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____14520 uu____14522)))
end
| uu____14523 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____14525 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____14525))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____14533 -> (match (uu____14533) with
| (x, imp) -> begin
(

let uu____14552 = (FStar_Syntax_Util.type_u ())
in (match (uu____14552) with
| (tu, u) -> begin
((

let uu____14572 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14572) with
| true -> begin
(

let uu____14573 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14574 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14575 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____14573 uu____14574 uu____14575))))
end
| uu____14576 -> begin
()
end));
(

let uu____14577 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____14577) with
| (t, uu____14597, g) -> begin
(

let x1 = (((

let uu___131_14605 = x
in {FStar_Syntax_Syntax.ppname = uu___131_14605.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_14605.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____14607 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____14607) with
| true -> begin
(

let uu____14608 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____14609 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____14608 uu____14609)))
end
| uu____14610 -> begin
()
end));
(

let uu____14611 = (push_binding env x1)
in ((x1), (uu____14611), (g), (u)));
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

let uu____14701 = (tc_binder env1 b)
in (match (uu____14701) with
| (b1, env', g, u) -> begin
(

let uu____14742 = (aux env' bs2)
in (match (uu____14742) with
| (bs3, env'1, g', us) -> begin
(

let uu____14795 = (

let uu____14796 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____14796))
in (((b1)::bs3), (env'1), (uu____14795), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____14881 uu____14882 -> (match (((uu____14881), (uu____14882))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____14951 = (tc_term env1 t)
in (match (uu____14951) with
| (t1, uu____14969, g') -> begin
(

let uu____14971 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____14971)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____15013 -> (match (uu____15013) with
| (pats1, g) -> begin
(

let uu____15038 = (tc_args env p)
in (match (uu____15038) with
| (args, g') -> begin
(

let uu____15051 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats1), (uu____15051)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____15064 = (tc_maybe_toplevel_term env e)
in (match (uu____15064) with
| (e1, c, g) -> begin
(

let uu____15080 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____15080) with
| true -> begin
((e1), (c), (g))
end
| uu____15087 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (c.FStar_Syntax_Syntax.comp ())
in (

let c2 = (norm_c env c1)
in (

let uu____15093 = (

let uu____15098 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____15098) with
| true -> begin
(

let uu____15103 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____15103), (false)))
end
| uu____15104 -> begin
(

let uu____15105 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____15105), (true)))
end))
in (match (uu____15093) with
| (target_comp, allow_ghost) -> begin
(

let uu____15114 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____15114) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____15124 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in ((e1), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (uu____15124)))
end
| uu____15125 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____15134 = (

let uu____15135 = (

let uu____15140 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in ((uu____15140), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____15135))
in (FStar_Exn.raise uu____15134))
end
| uu____15147 -> begin
(

let uu____15148 = (

let uu____15149 = (

let uu____15154 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in ((uu____15154), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____15149))
in (FStar_Exn.raise uu____15148))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____15173 = (tc_tot_or_gtot_term env t)
in (match (uu____15173) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____15203 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____15203) with
| true -> begin
(

let uu____15204 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____15204))
end
| uu____15205 -> begin
()
end));
(

let env1 = (

let uu___132_15207 = env
in {FStar_TypeChecker_Env.solver = uu___132_15207.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___132_15207.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___132_15207.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___132_15207.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___132_15207.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___132_15207.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___132_15207.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___132_15207.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___132_15207.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___132_15207.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___132_15207.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___132_15207.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___132_15207.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___132_15207.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___132_15207.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___132_15207.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___132_15207.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___132_15207.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___132_15207.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___132_15207.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___132_15207.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___132_15207.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___132_15207.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___132_15207.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___132_15207.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___132_15207.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___132_15207.FStar_TypeChecker_Env.identifier_info})
in (

let uu____15212 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)
with
| FStar_Errors.Error (msg, uu____15245) -> begin
(

let uu____15246 = (

let uu____15247 = (

let uu____15252 = (FStar_TypeChecker_Env.get_range env1)
in (((Prims.strcat "Implicit argument: " msg)), (uu____15252)))
in FStar_Errors.Error (uu____15247))
in (FStar_Exn.raise uu____15246))
end
in (match (uu____15212) with
| (t, c, g) -> begin
(

let uu____15268 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____15268) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____15277 -> begin
(

let uu____15278 = (

let uu____15279 = (

let uu____15284 = (

let uu____15285 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____15285))
in (

let uu____15286 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____15284), (uu____15286))))
in FStar_Errors.Error (uu____15279))
in (FStar_Exn.raise uu____15278))
end))
end)));
))


let level_of_type_fail : 'Auu____15301 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  'Auu____15301 = (fun env e t -> (

let uu____15314 = (

let uu____15315 = (

let uu____15320 = (

let uu____15321 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____15321 t))
in (

let uu____15322 = (FStar_TypeChecker_Env.get_range env)
in ((uu____15320), (uu____15322))))
in FStar_Errors.Error (uu____15315))
in (FStar_Exn.raise uu____15314)))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____15342 = (

let uu____15343 = (FStar_Syntax_Util.unrefine t1)
in uu____15343.FStar_Syntax_Syntax.n)
in (match (uu____15342) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____15347 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____15349 -> begin
(

let uu____15350 = (FStar_Syntax_Util.type_u ())
in (match (uu____15350) with
| (t_u, u) -> begin
(

let env1 = (

let uu___135_15358 = env
in {FStar_TypeChecker_Env.solver = uu___135_15358.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___135_15358.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___135_15358.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___135_15358.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___135_15358.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___135_15358.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___135_15358.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___135_15358.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___135_15358.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___135_15358.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___135_15358.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___135_15358.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___135_15358.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___135_15358.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___135_15358.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___135_15358.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___135_15358.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___135_15358.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___135_15358.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___135_15358.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___135_15358.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___135_15358.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___135_15358.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___135_15358.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___135_15358.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___135_15358.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___135_15358.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___135_15358.FStar_TypeChecker_Env.identifier_info})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____15362 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____15362))
end
| uu____15363 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____15374 = (

let uu____15375 = (FStar_Syntax_Subst.compress e)
in uu____15375.FStar_Syntax_Syntax.n)
in (match (uu____15374) with
| FStar_Syntax_Syntax.Tm_bvar (uu____15380) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____15385) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____15412) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____15428) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____15451, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____15478) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____15485 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____15485) with
| ((uu____15496, t), uu____15498) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____15503, (FStar_Util.Inl (t), uu____15505), uu____15506) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____15553, (FStar_Util.Inr (c), uu____15555), uu____15556) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____15606; FStar_Syntax_Syntax.vars = uu____15607}, us) -> begin
(

let uu____15613 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____15613) with
| ((us', t), uu____15626) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____15632 = (

let uu____15633 = (

let uu____15638 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____15638)))
in FStar_Errors.Error (uu____15633))
in (FStar_Exn.raise uu____15632))
end
| uu____15639 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____15654 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____15655) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____15665) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____15688 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____15688) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____15708 -> (match (uu____15708) with
| (b, uu____15714) -> begin
(

let uu____15715 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____15715))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____15720 = (universe_of_aux env res)
in (level_of_type env res uu____15720)))
in (

let u_c = (

let uu____15722 = (FStar_TypeChecker_Env.effect_repr env c1 u_res)
in (match (uu____15722) with
| FStar_Pervasives_Native.None -> begin
u_res
end
| FStar_Pervasives_Native.Some (trepr) -> begin
(

let uu____15726 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____15726))
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
| FStar_Syntax_Syntax.Tm_bvar (uu____15819) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____15834) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____15873) -> begin
(

let uu____15874 = (universe_of_aux env hd3)
in ((uu____15874), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____15887) -> begin
(

let uu____15888 = (universe_of_aux env hd3)
in ((uu____15888), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____15901) -> begin
(

let uu____15918 = (universe_of_aux env hd3)
in ((uu____15918), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____15931) -> begin
(

let uu____15938 = (universe_of_aux env hd3)
in ((uu____15938), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____15951) -> begin
(

let uu____15978 = (universe_of_aux env hd3)
in ((uu____15978), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____15991) -> begin
(

let uu____15998 = (universe_of_aux env hd3)
in ((uu____15998), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____16011) -> begin
(

let uu____16012 = (universe_of_aux env hd3)
in ((uu____16012), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____16025) -> begin
(

let uu____16038 = (universe_of_aux env hd3)
in ((uu____16038), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____16051) -> begin
(

let uu____16058 = (universe_of_aux env hd3)
in ((uu____16058), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____16071) -> begin
(

let uu____16072 = (universe_of_aux env hd3)
in ((uu____16072), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____16085, (hd4)::uu____16087) -> begin
(

let uu____16152 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____16152) with
| (uu____16167, uu____16168, hd5) -> begin
(

let uu____16186 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____16186) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____16237 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____16239 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____16239) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____16290 -> begin
(

let uu____16291 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____16291) with
| (env1, uu____16313) -> begin
(

let env2 = (

let uu___136_16319 = env1
in {FStar_TypeChecker_Env.solver = uu___136_16319.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___136_16319.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___136_16319.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___136_16319.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___136_16319.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___136_16319.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___136_16319.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___136_16319.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___136_16319.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___136_16319.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___136_16319.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___136_16319.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___136_16319.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___136_16319.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___136_16319.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___136_16319.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___136_16319.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___136_16319.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___136_16319.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___136_16319.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___136_16319.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___136_16319.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___136_16319.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___136_16319.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___136_16319.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___136_16319.FStar_TypeChecker_Env.identifier_info})
in ((

let uu____16321 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____16321) with
| true -> begin
(

let uu____16322 = (

let uu____16323 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____16323))
in (

let uu____16324 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____16322 uu____16324)))
end
| uu____16325 -> begin
()
end));
(

let uu____16326 = (tc_term env2 hd3)
in (match (uu____16326) with
| (uu____16347, {FStar_Syntax_Syntax.eff_name = uu____16348; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____16350; FStar_Syntax_Syntax.comp = uu____16351}, g) -> begin
((

let uu____16362 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____16362 FStar_Pervasives.ignore));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____16373 = (type_of_head true hd1 args)
in (match (uu____16373) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____16413 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____16413) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match (((FStar_List.length bs) = (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____16456 -> begin
(

let uu____16457 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____16457))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____16460, (hd1)::uu____16462) -> begin
(

let uu____16527 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____16527) with
| (uu____16530, uu____16531, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____16549, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____16594 = (universe_of_aux env e)
in (level_of_type env e uu____16594)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____16615 = (tc_binders env tps)
in (match (uu____16615) with
| (tps1, env1, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
((tps1), (env1), (us));
)
end)))




