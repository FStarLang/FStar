
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
| FStar_Syntax_Syntax.Tm_constant (uu____309) -> begin
false
end
| uu____310 -> begin
(

let uu____311 = (FStar_Syntax_Util.is_unit t1)
in (not (uu____311)))
end)))
end
| uu____312 -> begin
false
end))
end
| uu____313 -> begin
(

let uu____314 = (FStar_Syntax_Util.is_unit t)
in (not (uu____314)))
end)))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____317 = (

let uu____320 = ((

let uu____323 = (should_return t)
in (not (uu____323))) || (

let uu____325 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____325))))
in (match (uu____320) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____328 -> begin
(FStar_TypeChecker_Util.return_value env t e)
end))
in (FStar_Syntax_Util.lcomp_of_comp uu____317))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____333 = (

let uu____340 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____340) with
| FStar_Pervasives_Native.None -> begin
(((memo_tk e t)), (lc), (guard))
end
| FStar_Pervasives_Native.Some (t') -> begin
((

let uu____351 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____351) with
| true -> begin
(

let uu____352 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____353 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" uu____352 uu____353)))
end
| uu____354 -> begin
()
end));
(

let uu____355 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____355) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____371 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____371) with
| (e2, g) -> begin
((

let uu____385 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____385) with
| true -> begin
(

let uu____386 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____387 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____388 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____389 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____386 uu____387 uu____388 uu____389)))))
end
| uu____390 -> begin
()
end));
(

let msg = (

let uu____396 = (FStar_TypeChecker_Rel.is_trivial g)
in (match (uu____396) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____403 -> begin
(FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____413 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc1 g1)
in (match (uu____413) with
| (lc2, g2) -> begin
(((memo_tk e2 t')), ((set_lcomp_result lc2 t')), (g2))
end))));
)
end)))
end));
)
end))
in (match (uu____333) with
| (e1, lc1, g) -> begin
((

let uu____436 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____436) with
| true -> begin
(

let uu____437 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (FStar_Util.print1 "Return comp type is %s\n" uu____437))
end
| uu____438 -> begin
()
end));
((e1), (lc1), (g));
)
end))))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____463 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____463) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____473 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____473) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt uu____509 -> (match (uu____509) with
| (e, c) -> begin
(

let tot_or_gtot = (fun c1 -> (

let uu____538 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____538) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c1))
end
| uu____539 -> begin
(

let uu____540 = (FStar_Syntax_Util.is_pure_or_ghost_comp c1)
in (match (uu____540) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c1))
end
| uu____541 -> begin
(failwith "Impossible: Expected pure_or_ghost comp")
end))
end)))
in (

let uu____542 = (match (copt) with
| FStar_Pervasives_Native.Some (uu____555) -> begin
((copt), (c))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____558 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Parser_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____560 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____560)))))
in (match (uu____558) with
| true -> begin
(

let uu____567 = (

let uu____570 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____570))
in ((uu____567), (c)))
end
| uu____573 -> begin
(

let uu____574 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____574) with
| true -> begin
(

let uu____581 = (tot_or_gtot c)
in ((FStar_Pervasives_Native.None), (uu____581)))
end
| uu____584 -> begin
(

let uu____585 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____585) with
| true -> begin
(

let uu____592 = (

let uu____595 = (tot_or_gtot c)
in FStar_Pervasives_Native.Some (uu____595))
in ((uu____592), (c)))
end
| uu____598 -> begin
((FStar_Pervasives_Native.None), (c))
end))
end))
end))
end)
in (match (uu____542) with
| (expected_c_opt, c1) -> begin
(

let c2 = (norm_c env c1)
in (match (expected_c_opt) with
| FStar_Pervasives_Native.None -> begin
((e), (c2), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (expected_c) -> begin
(

let uu____621 = (FStar_TypeChecker_Util.check_comp env e c2 expected_c)
in (match (uu____621) with
| (e1, uu____635, g) -> begin
(

let g1 = (

let uu____638 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____638 "could not prove post-condition" g))
in ((

let uu____640 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____640) with
| true -> begin
(

let uu____641 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____642 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" uu____641 uu____642)))
end
| uu____643 -> begin
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


let no_logical_guard : 'Auu____653 'Auu____654 . FStar_TypeChecker_Env.env  ->  ('Auu____654 * 'Auu____653 * FStar_TypeChecker_Env.guard_t)  ->  ('Auu____654 * 'Auu____653 * FStar_TypeChecker_Env.guard_t) = (fun env uu____674 -> (match (uu____674) with
| (te, kt, f) -> begin
(

let uu____684 = (FStar_TypeChecker_Rel.guard_form f)
in (match (uu____684) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____692 = (

let uu____693 = (

let uu____698 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____699 = (FStar_TypeChecker_Env.get_range env)
in ((uu____698), (uu____699))))
in FStar_Errors.Error (uu____693))
in (FStar_Exn.raise uu____692))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let uu____710 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____710) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "Expected type is None\n")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____714 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____714))
end)))


let rec get_pat_vars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun pats acc -> (

let pats1 = (FStar_Syntax_Util.unmeta pats)
in (

let uu____738 = (FStar_Syntax_Util.head_and_args pats1)
in (match (uu____738) with
| (head1, args) -> begin
(

let uu____777 = (

let uu____778 = (FStar_Syntax_Util.un_uinst head1)
in uu____778.FStar_Syntax_Syntax.n)
in (match (uu____777) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
acc
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
(

let uu____785 = (FStar_List.tl args)
in (get_pat_vars_args uu____785 acc))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
(get_pat_vars_args args acc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(get_pat_vars_args args acc)
end
| uu____794 -> begin
(

let uu____795 = (FStar_Syntax_Free.names pats1)
in (FStar_Util.set_union acc uu____795))
end))
end))))
and get_pat_vars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun args acc -> (FStar_List.fold_left (fun s arg -> (get_pat_vars (FStar_Pervasives_Native.fst arg) s)) acc args))


let check_smt_pat : 'Auu____830 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * 'Auu____830) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.unit = (fun env t bs c -> (

let uu____863 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____863) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____864; FStar_Syntax_Syntax.effect_name = uu____865; FStar_Syntax_Syntax.result_typ = uu____866; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____870))::[]; FStar_Syntax_Syntax.flags = uu____871}) -> begin
(

let pat_vars = (

let uu____919 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (

let uu____920 = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
in (get_pat_vars uu____919 uu____920)))
in (

let uu____923 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____950 -> (match (uu____950) with
| (b, uu____956) -> begin
(

let uu____957 = (FStar_Util.set_mem b pat_vars)
in (not (uu____957)))
end))))
in (match (uu____923) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____963) -> begin
(

let uu____968 = (

let uu____969 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____969))
in (FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____968))
end)))
end
| uu____970 -> begin
(failwith "Impossible")
end)
end
| uu____971 -> begin
()
end)))


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (

let uu____1000 = (

let uu____1001 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____1001)))
in (match (uu____1000) with
| true -> begin
env.FStar_TypeChecker_Env.letrecs
end
| uu____1008 -> begin
(match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env1 = (

let uu___122_1032 = env
in {FStar_TypeChecker_Env.solver = uu___122_1032.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___122_1032.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___122_1032.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___122_1032.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___122_1032.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___122_1032.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___122_1032.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___122_1032.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___122_1032.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___122_1032.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___122_1032.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___122_1032.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___122_1032.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___122_1032.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___122_1032.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___122_1032.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___122_1032.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___122_1032.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___122_1032.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___122_1032.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___122_1032.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___122_1032.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___122_1032.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___122_1032.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___122_1032.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___122_1032.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___122_1032.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___122_1032.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___122_1032.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___122_1032.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___122_1032.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___122_1032.FStar_TypeChecker_Env.dsenv})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____1066 -> (match (uu____1066) with
| (b, uu____1074) -> begin
(

let t = (

let uu____1076 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____1076))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____1079) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1080) -> begin
[]
end
| uu____1093 -> begin
(

let uu____1094 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____1094)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____1099 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____1099) with
| (head1, uu____1115) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____1137 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____1141 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___115_1150 -> (match (uu___115_1150) with
| FStar_Syntax_Syntax.DECREASES (uu____1151) -> begin
true
end
| uu____1154 -> begin
false
end))))
in (match (uu____1141) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____1158 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____1167 -> begin
(mk_lex_list xs)
end))
end))))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____1184 -> (match (uu____1184) with
| (l, t) -> begin
(

let uu____1197 = (

let uu____1198 = (FStar_Syntax_Subst.compress t)
in uu____1198.FStar_Syntax_Syntax.n)
in (match (uu____1197) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____1257 -> (match (uu____1257) with
| (x, imp) -> begin
(

let uu____1268 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____1268) with
| true -> begin
(

let uu____1273 = (

let uu____1274 = (

let uu____1277 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____1277))
in (FStar_Syntax_Syntax.new_bv uu____1274 x.FStar_Syntax_Syntax.sort))
in ((uu____1273), (imp)))
end
| uu____1278 -> begin
((x), (imp))
end))
end))))
in (

let uu____1279 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____1279) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____1296 = (

let uu____1297 = (

let uu____1298 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____1299 = (

let uu____1302 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____1302)::[])
in (uu____1298)::uu____1299))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____1297))
in (uu____1296 FStar_Pervasives_Native.None r))
in (

let uu____1305 = (FStar_Util.prefix formals2)
in (match (uu____1305) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___123_1350 = last1
in (

let uu____1351 = (FStar_Syntax_Util.refine last1 precedes1)
in {FStar_Syntax_Syntax.ppname = uu___123_1350.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_1350.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1351}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____1377 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1377) with
| true -> begin
(

let uu____1378 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____1379 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1380 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____1378 uu____1379 uu____1380))))
end
| uu____1381 -> begin
()
end));
((l), (t'));
))))
end))))
end)))
end
| uu____1384 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let uu___124_1815 = env
in {FStar_TypeChecker_Env.solver = uu___124_1815.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___124_1815.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___124_1815.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___124_1815.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___124_1815.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___124_1815.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___124_1815.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___124_1815.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___124_1815.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___124_1815.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___124_1815.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___124_1815.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___124_1815.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___124_1815.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___124_1815.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___124_1815.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___124_1815.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___124_1815.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___124_1815.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___124_1815.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___124_1815.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___124_1815.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___124_1815.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___124_1815.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___124_1815.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___124_1815.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___124_1815.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___124_1815.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___124_1815.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___124_1815.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___124_1815.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___124_1815.FStar_TypeChecker_Env.dsenv}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (match ((Prims.op_Equality e.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____1825 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____1827 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1827) with
| true -> begin
(

let uu____1828 = (

let uu____1829 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1829))
in (

let uu____1830 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" uu____1828 uu____1830)))
end
| uu____1831 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1839) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1870) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1877) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1894) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____1895) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1896) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1897) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____1898) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1915) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____1928) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____1935) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____1936; FStar_Syntax_Syntax.vars = uu____1937}, FStar_Syntax_Syntax.Meta_alien (uu____1938, uu____1939, ty)) -> begin
(

let uu____1949 = (

let uu____1950 = (FStar_Syntax_Syntax.mk_Total ty)
in (FStar_All.pipe_right uu____1950 FStar_Syntax_Util.lcomp_of_comp))
in ((top), (uu____1949), (FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____1956 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____1956) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___125_1973 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___125_1973.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___125_1973.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___125_1973.FStar_TypeChecker_Env.implicits})
in ((e2), (c), (g1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____1990 = (FStar_Syntax_Util.type_u ())
in (match (uu____1990) with
| (t, u) -> begin
(

let uu____2003 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____2003) with
| (e2, c, g) -> begin
(

let uu____2019 = (

let uu____2034 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2034) with
| (env2, uu____2056) -> begin
(tc_pats env2 pats)
end))
in (match (uu____2019) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___126_2090 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___126_2090.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___126_2090.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___126_2090.FStar_TypeChecker_Env.implicits})
in (

let uu____2091 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2094 = (FStar_TypeChecker_Rel.conj_guard g g'1)
in ((uu____2091), (c), (uu____2094)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____2102 = (

let uu____2103 = (FStar_Syntax_Subst.compress e1)
in uu____2103.FStar_Syntax_Syntax.n)
in (match (uu____2102) with
| FStar_Syntax_Syntax.Tm_let ((uu____2112, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____2114; FStar_Syntax_Syntax.lbtyp = uu____2115; FStar_Syntax_Syntax.lbeff = uu____2116; FStar_Syntax_Syntax.lbdef = e11})::[]), e2) -> begin
(

let uu____2141 = (

let uu____2148 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (tc_term uu____2148 e11))
in (match (uu____2141) with
| (e12, c1, g1) -> begin
(

let uu____2158 = (tc_term env1 e2)
in (match (uu____2158) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e3 = (

let uu____2182 = (

let uu____2185 = (

let uu____2186 = (

let uu____2199 = (

let uu____2206 = (

let uu____2209 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_Syntax_Syntax.t_unit), (e13)))
in (uu____2209)::[])
in ((false), (uu____2206)))
in ((uu____2199), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____2186))
in (FStar_Syntax_Syntax.mk uu____2185))
in (uu____2182 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____2231 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e5), (c), (uu____2231)))))))))
end))
end))
end
| uu____2234 -> begin
(

let uu____2235 = (tc_term env1 e1)
in (match (uu____2235) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____2257)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____2274 = (tc_term env1 e1)
in (match (uu____2274) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____2298) -> begin
(

let uu____2345 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2345) with
| (env0, uu____2359) -> begin
(

let uu____2364 = (tc_comp env0 expected_c)
in (match (uu____2364) with
| (expected_c1, uu____2378, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c1)
in (

let uu____2383 = (

let uu____2390 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____2390 e1))
in (match (uu____2383) with
| (e2, c', g') -> begin
(

let uu____2400 = (

let uu____2407 = (

let uu____2412 = (c'.FStar_Syntax_Syntax.comp ())
in ((e2), (uu____2412)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____2407))
in (match (uu____2400) with
| (e3, expected_c2, g'') -> begin
(

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (t_res)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____2467 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____2467))
in (

let topt1 = (tc_tactic_opt env0 topt)
in (

let f1 = (match (topt1) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(FStar_TypeChecker_Rel.map_guard f (fun f1 -> (

let uu____2476 = (FStar_Syntax_Util.mk_squash f1)
in (FStar_TypeChecker_Common.mk_by_tactic tactic uu____2476))))
end)
in (

let uu____2477 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____2477) with
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
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____2497) -> begin
(

let uu____2544 = (FStar_Syntax_Util.type_u ())
in (match (uu____2544) with
| (k, u) -> begin
(

let uu____2557 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____2557) with
| (t1, uu____2571, f) -> begin
(

let uu____2573 = (

let uu____2580 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____2580 e1))
in (match (uu____2573) with
| (e2, c, g) -> begin
(

let uu____2590 = (

let uu____2595 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____2599 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____2595 e2 c f))
in (match (uu____2590) with
| (c1, f1) -> begin
(

let uu____2608 = (

let uu____2615 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____2615 c1))
in (match (uu____2608) with
| (e3, c2, f2) -> begin
(

let uu____2655 = (

let uu____2656 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____2656))
in ((e3), (c2), (uu____2655)))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____2657; FStar_Syntax_Syntax.vars = uu____2658}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____2721 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2721) with
| (unary_op, uu____2743) -> begin
(

let head1 = (

let uu____2767 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____2767))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____2805)); FStar_Syntax_Syntax.pos = uu____2806; FStar_Syntax_Syntax.vars = uu____2807}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____2870 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2870) with
| (unary_op, uu____2892) -> begin
(

let head1 = (

let uu____2916 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____2916))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____2954; FStar_Syntax_Syntax.vars = uu____2955}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____2987 -> begin
()
end);
(

let uu____2988 = (

let uu____2995 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2995) with
| (env0, uu____3009) -> begin
(tc_term env0 e1)
end))
in (match (uu____2988) with
| (e2, c, g) -> begin
(

let uu____3023 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3023) with
| (reify_op, uu____3045) -> begin
(

let u_c = (

let uu____3067 = (tc_term env1 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____3067) with
| (uu____3074, c', uu____3076) -> begin
(

let uu____3077 = (

let uu____3078 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____3078.FStar_Syntax_Syntax.n)
in (match (uu____3077) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____3082 -> begin
(

let uu____3083 = (FStar_Syntax_Util.type_u ())
in (match (uu____3083) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3095 = (

let uu____3096 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____3097 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____3098 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____3096 uu____3097 uu____3098))))
in (failwith uu____3095))
end);
u;
))
end))
end))
end))
in (

let repr = (

let uu____3100 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_TypeChecker_Env.reify_comp env1 uu____3100 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____3121 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____3121 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____3122 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____3122) with
| (e4, c2, g') -> begin
(

let uu____3138 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e4), (c2), (uu____3138)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.pos = uu____3140; FStar_Syntax_Syntax.vars = uu____3141}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____3173 -> begin
()
end);
(

let no_reflect = (fun uu____3183 -> (

let uu____3184 = (

let uu____3185 = (

let uu____3190 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((uu____3190), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____3185))
in (FStar_Exn.raise uu____3184)))
in (

let uu____3197 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____3197) with
| (reflect_op, uu____3219) -> begin
(

let uu____3240 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____3240) with
| FStar_Pervasives_Native.None -> begin
(no_reflect ())
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____3273 = (

let uu____3274 = (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____3274)))
in (match (uu____3273) with
| true -> begin
(no_reflect ())
end
| uu____3283 -> begin
(

let uu____3284 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3284) with
| (env_no_ex, topt) -> begin
(

let uu____3303 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____3323 = (

let uu____3326 = (

let uu____3327 = (

let uu____3342 = (

let uu____3345 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____3346 = (

let uu____3349 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____3349)::[])
in (uu____3345)::uu____3346))
in ((repr), (uu____3342)))
in FStar_Syntax_Syntax.Tm_app (uu____3327))
in (FStar_Syntax_Syntax.mk uu____3326))
in (uu____3323 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____3355 = (

let uu____3362 = (

let uu____3363 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____3363 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____3362 t))
in (match (uu____3355) with
| (t1, uu____3391, g) -> begin
(

let uu____3393 = (

let uu____3394 = (FStar_Syntax_Subst.compress t1)
in uu____3394.FStar_Syntax_Syntax.n)
in (match (uu____3393) with
| FStar_Syntax_Syntax.Tm_app (uu____3409, ((res, uu____3411))::((wp, uu____3413))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____3456 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____3303) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____3487 = (

let uu____3492 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____3492) with
| (e2, c, g) -> begin
((

let uu____3507 = (

let uu____3508 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____3508))
in (match (uu____3507) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 (((("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____3517 -> begin
()
end));
(

let uu____3518 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____3518) with
| FStar_Pervasives_Native.None -> begin
((

let uu____3526 = (

let uu____3533 = (

let uu____3538 = (

let uu____3539 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____3540 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____3539 uu____3540)))
in ((uu____3538), (e2.FStar_Syntax_Syntax.pos)))
in (uu____3533)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____3526));
(

let uu____3549 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e2), (uu____3549)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____3551 = (

let uu____3552 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____3552))
in ((e2), (uu____3551)))
end));
)
end))
in (match (uu____3487) with
| (e2, g) -> begin
(

let c = (

let uu____3562 = (

let uu____3563 = (

let uu____3564 = (

let uu____3565 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____3565)::[])
in (

let uu____3566 = (

let uu____3575 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3575)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____3564; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____3566; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____3563))
in (FStar_All.pipe_right uu____3562 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3595 = (comp_check_expected_typ env1 e3 c)
in (match (uu____3595) with
| (e4, c1, g') -> begin
(

let uu____3611 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e4), (c1), (uu____3611)))
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

let uu____3658 = (

let uu____3659 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____3659 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____3658 instantiate_both))
in ((

let uu____3675 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____3675) with
| true -> begin
(

let uu____3676 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3677 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____3676 uu____3677)))
end
| uu____3678 -> begin
()
end));
(

let isquote = (

let uu____3680 = (FStar_Syntax_Util.head_and_args head1)
in (match (uu____3680) with
| (head2, uu____3696) -> begin
(

let uu____3717 = (

let uu____3718 = (FStar_Syntax_Util.un_uinst head2)
in uu____3718.FStar_Syntax_Syntax.n)
in (match (uu____3717) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.quote_lid) -> begin
true
end
| uu____3722 -> begin
false
end))
end))
in (

let uu____3723 = (tc_term (no_inst env2) head1)
in (match (uu____3723) with
| (head2, chead, g_head) -> begin
(

let uu____3739 = (

let uu____3746 = ((not (env2.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____3746) with
| true -> begin
(

let uu____3753 = (

let uu____3760 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____3760))
in (match (uu____3753) with
| (e1, c, g) -> begin
(

let c1 = (

let uu____3773 = (((FStar_TypeChecker_Env.should_verify env2) && (

let uu____3775 = (FStar_Syntax_Util.is_lcomp_partial_return c)
in (not (uu____3775)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____3773) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e1 c)
end
| uu____3776 -> begin
c
end))
in ((e1), (c1), (g)))
end))
end
| uu____3777 -> begin
(

let env3 = (match (isquote) with
| true -> begin
(no_inst env2)
end
| uu____3779 -> begin
env2
end)
in (

let uu____3780 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env3 head2 chead g_head args uu____3780)))
end))
in (match (uu____3739) with
| (e1, c, g) -> begin
((

let uu____3793 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____3793) with
| true -> begin
(

let uu____3794 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____3794))
end
| uu____3795 -> begin
()
end));
(

let uu____3796 = (comp_check_expected_typ env0 e1 c)
in (match (uu____3796) with
| (e2, c1, g') -> begin
(

let gimp = (

let uu____3813 = (

let uu____3814 = (FStar_Syntax_Subst.compress head2)
in uu____3814.FStar_Syntax_Syntax.n)
in (match (uu____3813) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____3818) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e2), (c1.FStar_Syntax_Syntax.res_typ), (head2.FStar_Syntax_Syntax.pos))
in (

let uu___127_3880 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___127_3880.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___127_3880.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___127_3880.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____3929 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (

let uu____3931 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g uu____3931))
in ((

let uu____3933 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____3933) with
| true -> begin
(

let uu____3934 = (FStar_Syntax_Print.term_to_string e2)
in (

let uu____3935 = (FStar_TypeChecker_Rel.guard_to_string env2 gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____3934 uu____3935)))
end
| uu____3936 -> begin
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

let uu____3975 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3975) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____3995 = (tc_term env12 e1)
in (match (uu____3995) with
| (e11, c1, g1) -> begin
(

let uu____4011 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4021 = (FStar_Syntax_Util.type_u ())
in (match (uu____4021) with
| (k, uu____4031) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env1 k)
in (

let uu____4033 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in ((uu____4033), (res_t))))
end))
end)
in (match (uu____4011) with
| (env_branches, res_t) -> begin
((

let uu____4043 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____4043) with
| true -> begin
(

let uu____4044 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____4044))
end
| uu____4045 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____4130 = (

let uu____4135 = (FStar_List.fold_right (fun uu____4181 uu____4182 -> (match (((uu____4181), (uu____4182))) with
| ((uu____4245, f, c, g), (caccum, gaccum)) -> begin
(

let uu____4305 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (uu____4305)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____4135) with
| (cases, g) -> begin
(

let uu____4344 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____4344), (g)))
end))
in (match (uu____4130) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____4440 -> (match (uu____4440) with
| ((pat, wopt, br), uu____4468, lc, uu____4470) -> begin
(

let uu____4483 = (FStar_TypeChecker_Util.maybe_lift env1 br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (uu____4483)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____4538 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____4538) with
| true -> begin
(mk_match e11)
end
| uu____4541 -> begin
(

let e_match = (

let uu____4545 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____4545))
in (

let lb = (

let uu____4549 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = uu____4549; FStar_Syntax_Syntax.lbdef = e11})
in (

let e2 = (

let uu____4553 = (

let uu____4556 = (

let uu____4557 = (

let uu____4570 = (

let uu____4571 = (

let uu____4572 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____4572)::[])
in (FStar_Syntax_Subst.close uu____4571 e_match))
in ((((false), ((lb)::[]))), (uu____4570)))
in FStar_Syntax_Syntax.Tm_let (uu____4557))
in (FStar_Syntax_Syntax.mk uu____4556))
in (uu____4553 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____4585 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____4585) with
| true -> begin
(

let uu____4586 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____4587 = (

let uu____4588 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____4588))
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____4586 uu____4587)))
end
| uu____4589 -> begin
()
end));
(

let uu____4590 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e2), (cres), (uu____4590)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4593); FStar_Syntax_Syntax.lbunivs = uu____4594; FStar_Syntax_Syntax.lbtyp = uu____4595; FStar_Syntax_Syntax.lbeff = uu____4596; FStar_Syntax_Syntax.lbdef = uu____4597})::[]), uu____4598) -> begin
((

let uu____4618 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____4618) with
| true -> begin
(

let uu____4619 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____4619))
end
| uu____4620 -> begin
()
end));
(check_top_level_let env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____4621), uu____4622) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4637); FStar_Syntax_Syntax.lbunivs = uu____4638; FStar_Syntax_Syntax.lbtyp = uu____4639; FStar_Syntax_Syntax.lbeff = uu____4640; FStar_Syntax_Syntax.lbdef = uu____4641})::uu____4642), uu____4643) -> begin
((

let uu____4665 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____4665) with
| true -> begin
(

let uu____4666 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____4666))
end
| uu____4667 -> begin
()
end));
(check_top_level_let_rec env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____4668), uu____4669) -> begin
(check_inner_let_rec env1 top)
end));
)))
and tc_synth : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env args rng -> (

let uu____4695 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.None), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4785))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.Some (a)), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4845))))::((uu____4846, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4847))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
((tau), (FStar_Pervasives_Native.Some (a)), (rest))
end
| uu____4920 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("synth_by_tactic: bad application"), (rng)))))
end)
in (match (uu____4695) with
| (tau, atyp, rest) -> begin
(

let typ = (match (atyp) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5004 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____5004) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5010 = (

let uu____5011 = (

let uu____5016 = (FStar_TypeChecker_Env.get_range env)
in (("synth_by_tactic: need a type annotation when no expected type is present"), (uu____5016)))
in FStar_Errors.Error (uu____5011))
in (FStar_Exn.raise uu____5010))
end))
end)
in (

let uu____5019 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____5019) with
| (env', uu____5033) -> begin
(

let uu____5038 = (tc_term env' typ)
in (match (uu____5038) with
| (typ1, uu____5052, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g1);
(

let uu____5055 = (tc_tactic env' tau)
in (match (uu____5055) with
| (tau1, uu____5069, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g2);
(

let t = (match (env.FStar_TypeChecker_Env.nosynth) with
| true -> begin
(

let uu____5077 = (

let uu____5078 = (FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.magic_lid)
in (

let uu____5079 = (

let uu____5080 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____5080)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____5078 uu____5079)))
in (uu____5077 FStar_Pervasives_Native.None rng))
end
| uu____5083 -> begin
(

let t = (env.FStar_TypeChecker_Env.synth env' typ1 tau1)
in ((

let uu____5086 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____5086) with
| true -> begin
(

let uu____5087 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____5087))
end
| uu____5088 -> begin
()
end));
t;
))
end)
in ((FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(

let uu____5090 = (FStar_Syntax_Syntax.mk_Tm_app t rest FStar_Pervasives_Native.None rng)
in (tc_term env uu____5090));
));
)
end));
)
end))
end)))
end)))
and tc_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___128_5094 = env
in {FStar_TypeChecker_Env.solver = uu___128_5094.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___128_5094.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___128_5094.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___128_5094.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___128_5094.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___128_5094.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___128_5094.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___128_5094.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___128_5094.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___128_5094.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___128_5094.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___128_5094.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___128_5094.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___128_5094.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___128_5094.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___128_5094.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___128_5094.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___128_5094.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___128_5094.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___128_5094.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___128_5094.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___128_5094.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___128_5094.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___128_5094.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___128_5094.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___128_5094.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___128_5094.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___128_5094.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___128_5094.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___128_5094.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___128_5094.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___128_5094.FStar_TypeChecker_Env.dsenv})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit)))
and tc_reified_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___129_5098 = env
in {FStar_TypeChecker_Env.solver = uu___129_5098.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___129_5098.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___129_5098.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___129_5098.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___129_5098.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___129_5098.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___129_5098.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___129_5098.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___129_5098.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___129_5098.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___129_5098.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___129_5098.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___129_5098.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___129_5098.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___129_5098.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___129_5098.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___129_5098.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___129_5098.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___129_5098.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___129_5098.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___129_5098.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___129_5098.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___129_5098.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___129_5098.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___129_5098.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___129_5098.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___129_5098.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___129_5098.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___129_5098.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___129_5098.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___129_5098.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___129_5098.FStar_TypeChecker_Env.dsenv})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____5114 = (tc_tactic env tactic)
in (match (uu____5114) with
| (tactic1, uu____5124, uu____5125) -> begin
FStar_Pervasives_Native.Some (tactic1)
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t -> (

let uu____5164 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____5164) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____5185 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5185) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____5190 -> begin
(

let uu____5191 = (

let uu____5192 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5192))
in FStar_Util.Inr (uu____5191))
end))
in (

let is_data_ctor = (fun uu___116_5202 -> (match (uu___116_5202) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5205)) -> begin
true
end
| uu____5212 -> begin
false
end))
in (

let uu____5215 = ((is_data_ctor dc) && (

let uu____5217 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____5217))))
in (match (uu____5215) with
| true -> begin
(

let uu____5224 = (

let uu____5225 = (

let uu____5230 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____5231 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____5230), (uu____5231))))
in FStar_Errors.Error (uu____5225))
in (FStar_Exn.raise uu____5224))
end
| uu____5238 -> begin
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

let uu____5248 = (

let uu____5249 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____5249))
in (failwith uu____5248))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____5283 = (

let uu____5284 = (FStar_Syntax_Subst.compress t1)
in uu____5284.FStar_Syntax_Syntax.n)
in (match (uu____5283) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5287) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____5300 -> begin
(

let imp = (("uvar in term"), (env1), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___130_5338 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___130_5338.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___130_5338.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___130_5338.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env1 e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____5390 = (

let uu____5403 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____5403) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5418 = (FStar_Syntax_Util.type_u ())
in (match (uu____5418) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____5390) with
| (t, uu____5455, g0) -> begin
(

let uu____5469 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____5469) with
| (e1, uu____5489, g1) -> begin
(

let uu____5503 = (

let uu____5504 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____5504 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____5505 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e1), (uu____5503), (uu____5505))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____5507 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____5520 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____5520)))
end
| uu____5523 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____5507) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___131_5539 = x
in {FStar_Syntax_Syntax.ppname = uu___131_5539.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_5539.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Env.insert_bv_info env1 x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____5542 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____5542) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____5563 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5563) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____5568 -> begin
(

let uu____5569 = (

let uu____5570 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5570))
in FStar_Util.Inr (uu____5569))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5576; FStar_Syntax_Syntax.vars = uu____5577}, uu____5578) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____5583 = (

let uu____5584 = (

let uu____5589 = (FStar_TypeChecker_Env.get_range env1)
in (("Badly instantiated synth_by_tactic"), (uu____5589)))
in FStar_Errors.Error (uu____5584))
in (FStar_Exn.raise uu____5583))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____5597 = (

let uu____5598 = (

let uu____5603 = (FStar_TypeChecker_Env.get_range env1)
in (("Badly instantiated synth_by_tactic"), (uu____5603)))
in FStar_Errors.Error (uu____5598))
in (FStar_Exn.raise uu____5597))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5611; FStar_Syntax_Syntax.vars = uu____5612}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____5621 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5621) with
| ((us', t), range) -> begin
((match ((Prims.op_disEquality (FStar_List.length us1) (FStar_List.length us'))) with
| true -> begin
(

let uu____5644 = (

let uu____5645 = (

let uu____5650 = (

let uu____5651 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____5652 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____5653 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____5651 uu____5652 uu____5653))))
in (

let uu____5654 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____5650), (uu____5654))))
in FStar_Errors.Error (uu____5645))
in (FStar_Exn.raise uu____5644))
end
| uu____5655 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____5670 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____5674 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5674 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5676 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5676) with
| ((us, t), range) -> begin
((

let uu____5699 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____5699) with
| true -> begin
(

let uu____5700 = (

let uu____5701 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____5701))
in (

let uu____5702 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____5703 = (FStar_Range.string_of_range range)
in (

let uu____5704 = (FStar_Range.string_of_use_range range)
in (

let uu____5705 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____5700 uu____5702 uu____5703 uu____5704 uu____5705))))))
end
| uu____5706 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____5710 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5710 us))
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

let uu____5734 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____5734) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____5748 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5748) with
| (env2, uu____5762) -> begin
(

let uu____5767 = (tc_binders env2 bs1)
in (match (uu____5767) with
| (bs2, env3, g, us) -> begin
(

let uu____5786 = (tc_comp env3 c1)
in (match (uu____5786) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___132_5805 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___132_5805.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___132_5805.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____5814 = (FStar_TypeChecker_Rel.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Rel.conj_guard g uu____5814))
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

let uu____5833 = (

let uu____5838 = (

let uu____5839 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5839)::[])
in (FStar_Syntax_Subst.open_term uu____5838 phi))
in (match (uu____5833) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____5849 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5849) with
| (env2, uu____5863) -> begin
(

let uu____5868 = (

let uu____5881 = (FStar_List.hd x1)
in (tc_binder env2 uu____5881))
in (match (uu____5868) with
| (x2, env3, f1, u) -> begin
((

let uu____5909 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____5909) with
| true -> begin
(

let uu____5910 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____5911 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____5912 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____5910 uu____5911 uu____5912))))
end
| uu____5913 -> begin
()
end));
(

let uu____5914 = (FStar_Syntax_Util.type_u ())
in (match (uu____5914) with
| (t_phi, uu____5926) -> begin
(

let uu____5927 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____5927) with
| (phi2, uu____5941, f2) -> begin
(

let e1 = (

let uu___133_5946 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___133_5946.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___133_5946.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____5953 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____5953))
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____5966) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____5989 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____5989) with
| true -> begin
(

let uu____5990 = (FStar_Syntax_Print.term_to_string (

let uu___134_5993 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.pos = uu___134_5993.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___134_5993.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____5990))
end
| uu____5998 -> begin
()
end));
(

let uu____5999 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____5999) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____6012 -> begin
(

let uu____6013 = (

let uu____6014 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____6015 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____6014 uu____6015)))
in (failwith uu____6013))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Syntax_Syntax.t_unit
end
| FStar_Const.Const_bool (uu____6024) -> begin
FStar_Syntax_Util.t_bool
end
| FStar_Const.Const_int (uu____6025, FStar_Pervasives_Native.None) -> begin
FStar_Syntax_Syntax.t_int
end
| FStar_Const.Const_int (uu____6036, FStar_Pervasives_Native.Some (uu____6037)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____6052) -> begin
FStar_Syntax_Syntax.t_string
end
| FStar_Const.Const_float (uu____6057) -> begin
FStar_Syntax_Syntax.t_float
end
| FStar_Const.Const_char (uu____6058) -> begin
FStar_Syntax_Syntax.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____6059) -> begin
FStar_Syntax_Syntax.t_range
end
| uu____6060 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____6077) -> begin
(

let uu____6086 = (FStar_Syntax_Util.type_u ())
in (match (uu____6086) with
| (k, u) -> begin
(

let uu____6099 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____6099) with
| (t1, uu____6113, g) -> begin
(

let uu____6115 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____6115), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____6117) -> begin
(

let uu____6126 = (FStar_Syntax_Util.type_u ())
in (match (uu____6126) with
| (k, u) -> begin
(

let uu____6139 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____6139) with
| (t1, uu____6153, g) -> begin
(

let uu____6155 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____6155), (u), (g)))
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

let uu____6163 = (

let uu____6164 = (

let uu____6165 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____6165)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____6164))
in (uu____6163 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____6168 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____6168) with
| (tc1, uu____6182, f) -> begin
(

let uu____6184 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____6184) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____6228 = (

let uu____6229 = (FStar_Syntax_Subst.compress head3)
in uu____6229.FStar_Syntax_Syntax.n)
in (match (uu____6228) with
| FStar_Syntax_Syntax.Tm_uinst (uu____6232, us) -> begin
us
end
| uu____6238 -> begin
[]
end))
in (

let uu____6239 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____6239) with
| (uu____6260, args1) -> begin
(

let uu____6282 = (

let uu____6301 = (FStar_List.hd args1)
in (

let uu____6314 = (FStar_List.tl args1)
in ((uu____6301), (uu____6314))))
in (match (uu____6282) with
| (res, args2) -> begin
(

let uu____6379 = (

let uu____6388 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___117_6416 -> (match (uu___117_6416) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____6424 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____6424) with
| (env1, uu____6436) -> begin
(

let uu____6441 = (tc_tot_or_gtot_term env1 e)
in (match (uu____6441) with
| (e1, uu____6453, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____6388 FStar_List.unzip))
in (match (uu____6379) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___135_6492 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___135_6492.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___135_6492.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____6496 = (FStar_TypeChecker_Env.effect_repr env c2 u)
in (match (uu____6496) with
| FStar_Pervasives_Native.None -> begin
u
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____6500 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c2), (u_c), (uu____6500))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____6508) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____6509) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____6519 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____6519))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____6523 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____6523))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u2
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____6527 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____6528 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6528 FStar_Pervasives_Native.snd))
end
| uu____6537 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (

let uu____6561 = (

let uu____6562 = (

let uu____6567 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((uu____6567), (top.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____6562))
in (FStar_Exn.raise uu____6561)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____6657 bs2 bs_expected1 -> (match (uu____6657) with
| (env2, out, g, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.None), (g), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((match (((imp), (imp'))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6825))) -> begin
(

let uu____6830 = (

let uu____6831 = (

let uu____6836 = (

let uu____6837 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____6837))
in (

let uu____6838 = (FStar_Syntax_Syntax.range_of_bv hd1)
in ((uu____6836), (uu____6838))))
in FStar_Errors.Error (uu____6831))
in (FStar_Exn.raise uu____6830))
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6839)), FStar_Pervasives_Native.None) -> begin
(

let uu____6844 = (

let uu____6845 = (

let uu____6850 = (

let uu____6851 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____6851))
in (

let uu____6852 = (FStar_Syntax_Syntax.range_of_bv hd1)
in ((uu____6850), (uu____6852))))
in FStar_Errors.Error (uu____6845))
in (FStar_Exn.raise uu____6844))
end
| uu____6853 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____6859 = (

let uu____6864 = (

let uu____6865 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____6865.FStar_Syntax_Syntax.n)
in (match (uu____6864) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____6872 -> begin
((

let uu____6874 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____6874) with
| true -> begin
(

let uu____6875 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____6875))
end
| uu____6876 -> begin
()
end));
(

let uu____6877 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____6877) with
| (t, uu____6889, g1) -> begin
(

let g2 = (

let uu____6892 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____6893 = (FStar_TypeChecker_Rel.teq env2 t expected_t)
in (FStar_TypeChecker_Util.label_guard uu____6892 "Type annotation on parameter incompatible with the expected type" uu____6893)))
in (

let g3 = (

let uu____6895 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____6895))
in ((t), (g3))))
end));
)
end))
in (match (uu____6859) with
| (t, g1) -> begin
(

let hd2 = (

let uu___136_6923 = hd1
in {FStar_Syntax_Syntax.ppname = uu___136_6923.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_6923.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env3 = (push_binding env2 b)
in (

let subst2 = (

let uu____6936 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____6936))
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
| uu____7082 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____7089 = (tc_binders env1 bs)
in (match (uu____7089) with
| (bs1, envbody, g, uu____7119) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody), (body1), (g))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____7163 = (

let uu____7164 = (FStar_Syntax_Subst.compress t2)
in uu____7164.FStar_Syntax_Syntax.n)
in (match (uu____7163) with
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
| (bs1, envbody, g, uu____7248) -> begin
(

let uu____7249 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____7249) with
| (envbody1, uu____7277) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____7288); FStar_Syntax_Syntax.pos = uu____7289; FStar_Syntax_Syntax.vars = uu____7290}, uu____7291) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____7333 -> begin
(failwith "Impossible")
end);
(

let uu____7340 = (tc_binders env1 bs)
in (match (uu____7340) with
| (bs1, envbody, g, uu____7372) -> begin
(

let uu____7373 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____7373) with
| (envbody1, uu____7401) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____7413) -> begin
(

let uu____7418 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____7418) with
| (uu____7459, bs1, bs', copt, env2, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), (bs'), (copt), (env2), (body2), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____7502 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____7502) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 -> (

let rec handle_more = (fun uu____7602 c_expected2 -> (match (uu____7602) with
| (env3, bs2, more, guard, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7717 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env3), (bs2), (guard), (uu____7717)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____7748 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____7748))
in (

let uu____7749 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env3), (bs2), (guard), (uu____7749))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (

let uu____7774 = ((FStar_Options.ml_ish ()) || (FStar_Syntax_Util.is_named_tot c))
in (match (uu____7774) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env3 (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____7822 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____7822) with
| (bs_expected4, c_expected4) -> begin
(

let uu____7843 = (check_binders env3 more_bs bs_expected4)
in (match (uu____7843) with
| (env4, bs', more1, guard', subst2) -> begin
(

let uu____7891 = (

let uu____7922 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env4), ((FStar_List.append bs2 bs')), (more1), (uu____7922), (subst2)))
in (handle_more uu____7891 c_expected4))
end))
end))
end
| uu____7939 -> begin
(

let uu____7940 = (

let uu____7941 = (FStar_Syntax_Print.term_to_string t3)
in (FStar_Util.format1 "More arguments than annotated type (%s)" uu____7941))
in (fail uu____7940 t3))
end))
end
| uu____7956 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t2)
end)))
end)
end))
in (

let uu____7971 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____7971 c_expected1))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___137_8030 = envbody
in {FStar_TypeChecker_Env.solver = uu___137_8030.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___137_8030.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___137_8030.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___137_8030.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___137_8030.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___137_8030.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___137_8030.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___137_8030.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___137_8030.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___137_8030.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___137_8030.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___137_8030.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___137_8030.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___137_8030.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___137_8030.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___137_8030.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___137_8030.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___137_8030.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___137_8030.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___137_8030.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___137_8030.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___137_8030.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___137_8030.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___137_8030.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___137_8030.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___137_8030.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___137_8030.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___137_8030.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___137_8030.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___137_8030.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___137_8030.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___137_8030.FStar_TypeChecker_Env.dsenv})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____8069 uu____8070 -> (match (((uu____8069), (uu____8070))) with
| ((env2, letrec_binders), (l, t3)) -> begin
(

let uu____8115 = (

let uu____8122 = (

let uu____8123 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____8123 FStar_Pervasives_Native.fst))
in (tc_term uu____8122 t3))
in (match (uu____8115) with
| (t4, uu____8145, uu____8146) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l (([]), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____8156 = (FStar_Syntax_Syntax.mk_binder (

let uu___138_8159 = x
in {FStar_Syntax_Syntax.ppname = uu___138_8159.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___138_8159.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____8156)::letrec_binders)
end
| uu____8160 -> begin
letrec_binders
end)
in ((env3), (lb))))
end))
end)) ((envbody1), ([])))))))
in (

let uu____8165 = (check_actuals_against_formals env1 bs bs_expected1)
in (match (uu____8165) with
| (envbody, bs1, g, c) -> begin
(

let uu____8216 = (

let uu____8223 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____8223) with
| true -> begin
(mk_letrec_env envbody bs1 c)
end
| uu____8230 -> begin
((envbody), ([]))
end))
in (match (uu____8216) with
| (envbody1, letrecs) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in ((FStar_Pervasives_Native.Some (t2)), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (envbody2), (body1), (g)))
end))
end))))
end))
end
| uu____8272 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____8293 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____8293))
end
| uu____8294 -> begin
(

let uu____8295 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____8295) with
| (uu____8334, bs1, uu____8336, c_opt, envbody, body2, g) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (c_opt), (envbody), (body2), (g))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____8356 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8356) with
| (env1, topt) -> begin
((

let uu____8376 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____8376) with
| true -> begin
(

let uu____8377 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____8377 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____8379 -> begin
"false"
end)))
end
| uu____8380 -> begin
()
end));
(

let uu____8381 = (expected_function_typ1 env1 topt body)
in (match (uu____8381) with
| (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1, g) -> begin
(

let uu____8421 = (

let should_check_expected_effect = (

let uu____8429 = (

let uu____8436 = (

let uu____8437 = (FStar_Syntax_Subst.compress body1)
in uu____8437.FStar_Syntax_Syntax.n)
in ((c_opt), (uu____8436)))
in (match (uu____8429) with
| (FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Tm_ascribed (uu____8442, (FStar_Util.Inr (expected_c), uu____8444), uu____8445)) -> begin
false
end
| uu____8494 -> begin
true
end))
in (

let uu____8501 = (tc_term (

let uu___139_8510 = envbody
in {FStar_TypeChecker_Env.solver = uu___139_8510.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___139_8510.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___139_8510.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___139_8510.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___139_8510.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___139_8510.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___139_8510.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___139_8510.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___139_8510.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___139_8510.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___139_8510.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___139_8510.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___139_8510.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___139_8510.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___139_8510.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___139_8510.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___139_8510.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___139_8510.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___139_8510.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___139_8510.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___139_8510.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___139_8510.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___139_8510.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___139_8510.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___139_8510.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___139_8510.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___139_8510.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___139_8510.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___139_8510.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___139_8510.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___139_8510.FStar_TypeChecker_Env.dsenv}) body1)
in (match (uu____8501) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (match (should_check_expected_effect) with
| true -> begin
(

let uu____8527 = (

let uu____8534 = (

let uu____8539 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body2), (uu____8539)))
in (check_expected_effect (

let uu___140_8546 = envbody
in {FStar_TypeChecker_Env.solver = uu___140_8546.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___140_8546.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___140_8546.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___140_8546.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___140_8546.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___140_8546.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___140_8546.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___140_8546.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___140_8546.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___140_8546.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___140_8546.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___140_8546.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___140_8546.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___140_8546.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___140_8546.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___140_8546.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___140_8546.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___140_8546.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___140_8546.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___140_8546.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___140_8546.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___140_8546.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___140_8546.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___140_8546.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___140_8546.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___140_8546.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___140_8546.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___140_8546.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___140_8546.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___140_8546.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___140_8546.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___140_8546.FStar_TypeChecker_Env.dsenv}) c_opt uu____8534))
in (match (uu____8527) with
| (body3, cbody1, guard) -> begin
(

let uu____8556 = (FStar_TypeChecker_Rel.conj_guard guard_body1 guard)
in ((body3), (cbody1), (uu____8556)))
end))
end
| uu____8557 -> begin
(

let uu____8558 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body2), (uu____8558), (guard_body1)))
end))
end)))
in (match (uu____8421) with
| (body2, cbody, guard) -> begin
(

let guard1 = (

let uu____8573 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____8575 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____8575))))
in (match (uu____8573) with
| true -> begin
(

let uu____8576 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____8576))
end
| uu____8577 -> begin
(

let guard1 = (

let uu____8579 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard env1 (FStar_List.append bs1 letrec_binders) uu____8579))
in guard1)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody)
in (

let e = (FStar_Syntax_Util.abs bs1 body2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody c_opt)))))
in (

let uu____8588 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____8609) -> begin
((e), (t1), (guard1))
end
| uu____8622 -> begin
(

let uu____8623 = (FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
in (match (uu____8623) with
| (e1, guard') -> begin
(

let uu____8636 = (FStar_TypeChecker_Rel.conj_guard guard1 guard')
in ((e1), (t1), (uu____8636)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard1))
end)
in (match (uu____8588) with
| (e1, tfun, guard2) -> begin
(

let c = (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____8649 -> begin
(FStar_TypeChecker_Util.return_value env1 tfun e1)
end)
in (

let uu____8650 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 (FStar_Syntax_Util.lcomp_of_comp c) guard2)
in (match (uu____8650) with
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

let uu____8699 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8699) with
| true -> begin
(

let uu____8700 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____8701 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____8700 uu____8701)))
end
| uu____8702 -> begin
()
end));
(

let monadic_application = (fun uu____8758 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____8758) with
| (head2, chead1, ghead1, cres) -> begin
(

let rt = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres1 = (

let uu___141_8817 = cres
in {FStar_Syntax_Syntax.eff_name = uu___141_8817.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___141_8817.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___141_8817.FStar_Syntax_Syntax.comp})
in (

let uu____8818 = (match (bs) with
| [] -> begin
(

let cres2 = (FStar_TypeChecker_Util.subst_lcomp subst1 cres1)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in ((cres2), (g))))
end
| uu____8833 -> begin
(

let g = (

let uu____8841 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____8841 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (

let uu____8842 = (

let uu____8843 = (

let uu____8846 = (

let uu____8847 = (

let uu____8848 = (cres1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs uu____8848))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst1) uu____8847))
in (FStar_Syntax_Syntax.mk_Total uu____8846))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8843))
in ((uu____8842), (g))))
end)
in (match (uu____8818) with
| (cres2, guard1) -> begin
((

let uu____8862 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____8862) with
| true -> begin
(

let uu____8863 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____8863))
end
| uu____8864 -> begin
()
end));
(

let cres3 = (

let uu____8866 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2)
in (match (uu____8866) with
| true -> begin
(

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2))
end
| uu____8876 -> begin
cres2
end))
in (

let comp = (FStar_List.fold_left (fun out_c uu____8900 -> (match (uu____8900) with
| ((e, q), x, c) -> begin
(

let uu____8933 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____8933) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____8938 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end))
end)) cres3 arg_comps_rev)
in (

let comp1 = (FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
in (

let shortcuts_evaluation_order = (

let uu____8945 = (

let uu____8946 = (FStar_Syntax_Subst.compress head2)
in uu____8946.FStar_Syntax_Syntax.n)
in (match (uu____8945) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____8950 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____8971 -> (match (uu____8971) with
| (arg, uu____8985, uu____8986) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ))))
end
| uu____8995 -> begin
(

let uu____8996 = (

let map_fun = (fun uu____9058 -> (match (uu____9058) with
| ((e, q), uu____9093, c) -> begin
(

let uu____9103 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____9103) with
| true -> begin
((FStar_Pervasives_Native.None), (((e), (q))))
end
| uu____9150 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____9153 = (

let uu____9158 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____9158), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____9153)))))
end))
end))
in (

let uu____9187 = (

let uu____9212 = (

let uu____9235 = (

let uu____9250 = (

let uu____9259 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____9259), (FStar_Pervasives_Native.None), (chead1)))
in (uu____9250)::arg_comps_rev)
in (FStar_List.map map_fun uu____9235))
in (FStar_All.pipe_left FStar_List.split uu____9212))
in (match (uu____9187) with
| (lifted_args, reverse_args) -> begin
(

let uu____9432 = (

let uu____9433 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____9433))
in (

let uu____9442 = (

let uu____9449 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____9449))
in ((lifted_args), (uu____9432), (uu____9442))))
end)))
in (match (uu____8996) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___118_9552 -> (match (uu___118_9552) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1)
in (

let letbinding = (

let uu____9607 = (

let uu____9610 = (

let uu____9611 = (

let uu____9624 = (

let uu____9625 = (

let uu____9626 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____9626)::[])
in (FStar_Syntax_Subst.close uu____9625 e))
in ((((false), ((lb)::[]))), (uu____9624)))
in FStar_Syntax_Syntax.Tm_let (uu____9611))
in (FStar_Syntax_Syntax.mk uu____9610))
in (uu____9607 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp1.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____9656 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp1 guard1)
in (match (uu____9656) with
| (comp2, g) -> begin
((app), (comp2), (g))
end)))))));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____9747 bs args1 -> (match (uu____9747) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9894))))::rest, ((uu____9896, FStar_Pervasives_Native.None))::uu____9897) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let t1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (

let uu____9958 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____9958) with
| (varg, uu____9978, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____10000 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____10000)))
in (

let uu____10001 = (

let uu____10036 = (

let uu____10051 = (

let uu____10064 = (

let uu____10065 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____10065 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____10064)))
in (uu____10051)::outargs)
in (

let uu____10084 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst2), (uu____10036), ((arg)::arg_rets), (uu____10084), (fvs))))
in (tc_args head_info uu____10001 rest args1))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10186)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10187))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____10200 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___142_10211 = x
in {FStar_Syntax_Syntax.ppname = uu___142_10211.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_10211.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____10213 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____10213) with
| true -> begin
(

let uu____10214 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____10214))
end
| uu____10215 -> begin
()
end));
(

let targ1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___143_10219 = env1
in {FStar_TypeChecker_Env.solver = uu___143_10219.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___143_10219.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___143_10219.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___143_10219.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___143_10219.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___143_10219.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___143_10219.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___143_10219.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___143_10219.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___143_10219.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___143_10219.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___143_10219.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___143_10219.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___143_10219.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___143_10219.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___143_10219.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___143_10219.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___143_10219.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___143_10219.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___143_10219.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___143_10219.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___143_10219.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___143_10219.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___143_10219.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___143_10219.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___143_10219.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___143_10219.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___143_10219.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___143_10219.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___143_10219.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___143_10219.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___143_10219.FStar_TypeChecker_Env.dsenv})
in ((

let uu____10221 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____10221) with
| true -> begin
(

let uu____10222 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____10223 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____10224 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____10222 uu____10223 uu____10224))))
end
| uu____10225 -> begin
()
end));
(

let uu____10226 = (tc_term env2 e)
in (match (uu____10226) with
| (e1, c, g_e) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____10253 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____10253))
in (

let uu____10254 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____10254) with
| true -> begin
(

let subst2 = (

let uu____10262 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____10262 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____10311 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
))));
)));
)
end
| (uu____10356, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____10392) -> begin
(

let uu____10443 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____10443) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 tres -> (

let tres1 = (

let uu____10477 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____10477 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____10502 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____10502) with
| (bs2, cres'1) -> begin
(

let head_info1 = ((head2), (chead1), (ghead1), ((FStar_Syntax_Util.lcomp_of_comp cres'1)))
in ((

let uu____10525 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____10525) with
| true -> begin
(FStar_Errors.warn tres1.FStar_Syntax_Syntax.pos "Potentially redundant explicit currying of a function type")
end
| uu____10526 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____10567 when (not (norm1)) -> begin
(

let uu____10568 = (FStar_TypeChecker_Normalize.unfold_whnf env tres1)
in (aux true uu____10568))
end
| uu____10569 -> begin
(

let uu____10570 = (

let uu____10571 = (

let uu____10576 = (

let uu____10577 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____10578 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" uu____10577 uu____10578)))
in (

let uu____10585 = (FStar_Syntax_Syntax.argpos arg)
in ((uu____10576), (uu____10585))))
in FStar_Errors.Error (uu____10571))
in (FStar_Exn.raise uu____10570))
end)))
in (aux false chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf -> (

let uu____10604 = (

let uu____10605 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____10605.FStar_Syntax_Syntax.n)
in (match (uu____10604) with
| FStar_Syntax_Syntax.Tm_uvar (uu____10616) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____10717 = (tc_term env1 e)
in (match (uu____10717) with
| (e1, c, g_e) -> begin
(

let uu____10739 = (tc_args1 env1 tl1)
in (match (uu____10739) with
| (args2, comps, g_rest) -> begin
(

let uu____10779 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____10779)))
end))
end))
end))
in (

let uu____10800 = (tc_args1 env args)
in (match (uu____10800) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____10837 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____10875 -> (match (uu____10875) with
| (uu____10888, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____10837))
in (

let ml_or_tot = (fun t r1 -> (

let uu____10905 = (FStar_Options.ml_ish ())
in (match (uu____10905) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____10906 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____10908 = (

let uu____10911 = (

let uu____10912 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____10912 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____10911))
in (ml_or_tot uu____10908 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____10925 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____10925) with
| true -> begin
(

let uu____10926 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____10927 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____10928 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____10926 uu____10927 uu____10928))))
end
| uu____10929 -> begin
()
end));
(

let uu____10931 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____10931));
(

let comp = (

let uu____10933 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____10944 out -> (match (uu____10944) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____10933))
in (

let uu____10958 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let uu____10961 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____10958), (comp), (uu____10961)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____10964); FStar_Syntax_Syntax.pos = uu____10965; FStar_Syntax_Syntax.vars = uu____10966}, uu____10967) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____11088 = (tc_term env1 e)
in (match (uu____11088) with
| (e1, c, g_e) -> begin
(

let uu____11110 = (tc_args1 env1 tl1)
in (match (uu____11110) with
| (args2, comps, g_rest) -> begin
(

let uu____11150 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____11150)))
end))
end))
end))
in (

let uu____11171 = (tc_args1 env args)
in (match (uu____11171) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____11208 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____11246 -> (match (uu____11246) with
| (uu____11259, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____11208))
in (

let ml_or_tot = (fun t r1 -> (

let uu____11276 = (FStar_Options.ml_ish ())
in (match (uu____11276) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____11277 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____11279 = (

let uu____11282 = (

let uu____11283 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____11283 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____11282))
in (ml_or_tot uu____11279 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____11296 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____11296) with
| true -> begin
(

let uu____11297 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____11298 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____11299 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____11297 uu____11298 uu____11299))))
end
| uu____11300 -> begin
()
end));
(

let uu____11302 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____11302));
(

let comp = (

let uu____11304 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____11315 out -> (match (uu____11315) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____11304))
in (

let uu____11329 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let uu____11332 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____11329), (comp), (uu____11332)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____11353 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____11353) with
| (bs1, c1) -> begin
(

let head_info = ((head1), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c1)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs1 args))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____11418) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____11424, uu____11425) -> begin
(check_function_app t)
end
| uu____11466 -> begin
(

let uu____11467 = (

let uu____11468 = (

let uu____11473 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((uu____11473), (head1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____11468))
in (FStar_Exn.raise uu____11467))
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

let uu____11543 = (FStar_List.fold_left2 (fun uu____11586 uu____11587 uu____11588 -> (match (((uu____11586), (uu____11587), (uu____11588))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((Prims.op_disEquality aq aq')) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____11655 -> begin
()
end);
(

let uu____11656 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____11656) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____11674 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____11674 g))
in (

let ghost1 = (ghost || ((

let uu____11678 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____11678))) && (

let uu____11680 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____11680)))))
in (

let uu____11681 = (

let uu____11690 = (

let uu____11699 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____11699)::[])
in (FStar_List.append seen uu____11690))
in (

let uu____11706 = (FStar_TypeChecker_Rel.conj_guard guard g1)
in ((uu____11681), (uu____11706), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____11543) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____11742 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____11742 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____11743 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____11744 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____11744) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____11761 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____11795 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____11795) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____11831 = branch1
in (match (uu____11831) with
| (cpat, uu____11863, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let tc_annot = (fun env1 t -> (

let uu____11922 = (FStar_Syntax_Util.type_u ())
in (match (uu____11922) with
| (tu, u) -> begin
(

let uu____11929 = (tc_check_tot_or_gtot_term env1 t tu)
in (match (uu____11929) with
| (t1, uu____11937, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
t1;
)
end))
end)))
in (

let uu____11940 = (FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 tc_annot)
in (match (uu____11940) with
| (pat_bvs1, exp, p) -> begin
((

let uu____11969 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____11969) with
| true -> begin
(

let uu____11970 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____11971 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____11970 uu____11971)))
end
| uu____11972 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs1)
in (

let uu____11974 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____11974) with
| (env1, uu____11994) -> begin
(

let env11 = (

let uu___144_12000 = env1
in {FStar_TypeChecker_Env.solver = uu___144_12000.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___144_12000.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___144_12000.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___144_12000.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___144_12000.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___144_12000.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___144_12000.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___144_12000.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___144_12000.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___144_12000.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___144_12000.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___144_12000.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___144_12000.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___144_12000.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___144_12000.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___144_12000.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___144_12000.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___144_12000.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___144_12000.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___144_12000.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___144_12000.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___144_12000.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___144_12000.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___144_12000.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___144_12000.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___144_12000.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___144_12000.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___144_12000.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___144_12000.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___144_12000.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___144_12000.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___144_12000.FStar_TypeChecker_Env.dsenv})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in ((

let uu____12003 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____12003) with
| true -> begin
(

let uu____12004 = (FStar_Syntax_Print.term_to_string exp)
in (

let uu____12005 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____12004 uu____12005)))
end
| uu____12006 -> begin
()
end));
(

let env12 = (FStar_TypeChecker_Env.set_expected_typ env11 expected_pat_t)
in (

let uu____12008 = (tc_tot_or_gtot_term env12 exp)
in (match (uu____12008) with
| (exp1, lc, g) -> begin
(

let g1 = (

let uu___145_12031 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___145_12031.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___145_12031.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___145_12031.FStar_TypeChecker_Env.implicits})
in (

let uu____12032 = (

let uu____12033 = (FStar_TypeChecker_Rel.teq_nosmt env12 lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (match (uu____12033) with
| true -> begin
(

let env13 = (FStar_TypeChecker_Env.set_range env12 exp1.FStar_Syntax_Syntax.pos)
in (

let uu____12035 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env13 g1)
in (FStar_All.pipe_right uu____12035 FStar_TypeChecker_Rel.resolve_implicits)))
end
| uu____12036 -> begin
(

let uu____12037 = (

let uu____12038 = (

let uu____12043 = (

let uu____12044 = (FStar_Syntax_Print.term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____12045 = (FStar_Syntax_Print.term_to_string expected_pat_t)
in (FStar_Util.format2 "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)" uu____12044 uu____12045)))
in ((uu____12043), (exp1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____12038))
in (FStar_Exn.raise uu____12037))
end))
in (

let norm_exp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env12 exp1)
in (

let uvs1 = (FStar_Syntax_Free.uvars norm_exp)
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____12062 = (

let uu____12063 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____12063))
in (match (uu____12062) with
| true -> begin
(

let unresolved = (

let uu____12075 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right uu____12075 FStar_Util.set_elements))
in (

let uu____12102 = (

let uu____12103 = (

let uu____12108 = (

let uu____12109 = (FStar_TypeChecker_Normalize.term_to_string env norm_exp)
in (

let uu____12110 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____12111 = (

let uu____12112 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____12130 -> (match (uu____12130) with
| (u, uu____12136) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____12112 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____12109 uu____12110 uu____12111))))
in ((uu____12108), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____12103))
in (FStar_Exn.raise uu____12102)))
end
| uu____12139 -> begin
()
end));
(

let uu____12141 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____12141) with
| true -> begin
(

let uu____12142 = (FStar_TypeChecker_Normalize.term_to_string env exp1)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____12142))
end
| uu____12143 -> begin
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

let uu____12151 = (

let uu____12158 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____12158 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____12151) with
| (scrutinee_env, uu____12182) -> begin
(

let uu____12187 = (tc_pat true pat_t pattern)
in (match (uu____12187) with
| (pattern1, pat_bvs1, pat_env, pat_exp, norm_pat_exp) -> begin
(

let uu____12225 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____12247 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____12247) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____12260 -> begin
(

let uu____12261 = (

let uu____12268 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_Syntax_Util.t_bool)
in (tc_term uu____12268 e))
in (match (uu____12261) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____12225) with
| (when_clause1, g_when) -> begin
(

let uu____12302 = (tc_term pat_env branch_exp)
in (match (uu____12302) with
| (branch_exp1, c, g_branch) -> begin
(

let when_condition = (match (when_clause1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____12334 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____12334))
end)
in (

let uu____12337 = (

let eqs = (

let uu____12347 = (

let uu____12348 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12348)))
in (match (uu____12347) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12351 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____12355) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____12372) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____12373) -> begin
FStar_Pervasives_Native.None
end
| uu____12374 -> begin
(

let uu____12375 = (

let uu____12376 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____12376 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____12375))
end))
end))
in (

let uu____12377 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch)
in (match (uu____12377) with
| (c1, g_branch1) -> begin
(

let uu____12392 = (match (((eqs), (when_condition))) with
| uu____12405 when (

let uu____12414 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12414))) -> begin
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

let uu____12426 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____12427 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____12426), (uu____12427))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____12436 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____12436))
in (

let uu____12437 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____12438 = (

let uu____12439 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____12439 g_when))
in ((uu____12437), (uu____12438))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____12447 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____12447), (g_when)))))
end)
in (match (uu____12392) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let uu____12459 = (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak)
in (

let uu____12460 = (FStar_TypeChecker_Rel.close_guard env binders g_when_weak)
in ((uu____12459), (uu____12460), (g_branch1)))))
end))
end)))
in (match (uu____12337) with
| (c1, g_when1, g_branch1) -> begin
(

let branch_guard = (

let uu____12481 = (

let uu____12482 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12482)))
in (match (uu____12481) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____12483 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____12512 = (

let uu____12513 = (

let uu____12514 = (

let uu____12517 = (

let uu____12524 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____12524))
in (FStar_Pervasives_Native.snd uu____12517))
in (FStar_List.length uu____12514))
in (uu____12513 > (Prims.parse_int "1")))
in (match (uu____12512) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____12530 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____12530) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____12551 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____12566 = (

let uu____12567 = (

let uu____12568 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____12568)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____12567))
in (uu____12566 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____12571 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____12571)::[])))
end)))
end
| uu____12572 -> begin
[]
end)))
in (

let fail = (fun uu____12576 -> (

let uu____12577 = (

let uu____12578 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____12579 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____12580 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____12578 uu____12579 uu____12580))))
in (failwith uu____12577)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____12591) -> begin
(head_constructor t1)
end
| uu____12596 -> begin
(fail ())
end))
in (

let pat_exp2 = (

let uu____12598 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____12598 FStar_Syntax_Util.unmeta))
in (match (pat_exp2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____12601) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12618); FStar_Syntax_Syntax.pos = uu____12619; FStar_Syntax_Syntax.vars = uu____12620}, uu____12621) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_name (uu____12658) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (c2) -> begin
(

let uu____12660 = (

let uu____12661 = (tc_constant pat_exp2.FStar_Syntax_Syntax.pos c2)
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____12661 scrutinee_tm1 pat_exp2))
in (uu____12660)::[])
end
| FStar_Syntax_Syntax.Tm_uinst (uu____12662) -> begin
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
| FStar_Syntax_Syntax.Tm_fvar (uu____12678) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____12680 = (

let uu____12681 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____12681)))
in (match (uu____12680) with
| true -> begin
[]
end
| uu____12684 -> begin
(

let uu____12685 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____12685))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let f = (head_constructor head1)
in (

let uu____12711 = (

let uu____12712 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____12712)))
in (match (uu____12711) with
| true -> begin
[]
end
| uu____12715 -> begin
(

let sub_term_guards = (

let uu____12719 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____12751 -> (match (uu____12751) with
| (ei, uu____12761) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____12767 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____12767) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____12788 -> begin
(

let sub_term = (

let uu____12802 = (

let uu____12803 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____12804 = (

let uu____12805 = (FStar_Syntax_Syntax.as_arg scrutinee_tm1)
in (uu____12805)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____12803 uu____12804)))
in (uu____12802 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____12719 FStar_List.flatten))
in (

let uu____12814 = (discriminate scrutinee_tm1 f)
in (FStar_List.append uu____12814 sub_term_guards)))
end)))
end
| uu____12817 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pat -> (

let uu____12829 = (

let uu____12830 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12830)))
in (match (uu____12829) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____12831 -> begin
(

let t = (

let uu____12833 = (build_branch_guard scrutinee_tm1 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____12833))
in (

let uu____12838 = (FStar_Syntax_Util.type_u ())
in (match (uu____12838) with
| (k, uu____12844) -> begin
(

let uu____12845 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____12845) with
| (t1, uu____12853, uu____12854) -> begin
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

let uu____12860 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____12860) with
| true -> begin
(

let uu____12861 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____12861))
end
| uu____12862 -> begin
()
end));
(

let uu____12863 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in ((uu____12863), (branch_guard), (c1), (guard)));
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

let uu____12889 = (check_let_bound_def true env1 lb)
in (match (uu____12889) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____12911 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____12928 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____12928), (univ_vars1), (c1)))
end
| uu____12929 -> begin
(

let g11 = (

let uu____12931 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____12931 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____12935 = (

let uu____12948 = (

let uu____12963 = (

let uu____12972 = (

let uu____12985 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____12985)))
in (uu____12972)::[])
in (FStar_TypeChecker_Util.generalize env1 false uu____12963))
in (FStar_List.hd uu____12948))
in (match (uu____12935) with
| (uu____13038, univs1, e11, c11, gvs) -> begin
(

let g12 = (FStar_All.pipe_left (FStar_TypeChecker_Rel.map_guard g11) (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env1))
in (

let g13 = (FStar_TypeChecker_Rel.abstract_guard_n gvs g12)
in ((g13), (e11), (univs1), ((FStar_Syntax_Util.lcomp_of_comp c11)))))
end)))
end)
in (match (uu____12911) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____13061 = (

let uu____13068 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____13068) with
| true -> begin
(

let uu____13075 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____13075) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____13096 -> begin
((

let uu____13098 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.warn uu____13098 FStar_TypeChecker_Err.top_level_effect));
(

let uu____13099 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____13099), (c12)));
)
end)
end))
end
| uu____13106 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____13109 = (c11.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right uu____13109 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env1)))
in (

let e21 = (

let uu____13117 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____13117) with
| true -> begin
e2
end
| uu____13120 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end))
in ((e21), (c))));
)
end))
in (match (uu____13061) with
| (e21, c12) -> begin
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit)
in (

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e11)
in (

let uu____13141 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in ((uu____13141), ((FStar_Syntax_Util.lcomp_of_comp cres)), (FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| uu____13156 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___146_13187 = env1
in {FStar_TypeChecker_Env.solver = uu___146_13187.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___146_13187.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___146_13187.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___146_13187.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___146_13187.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___146_13187.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___146_13187.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___146_13187.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___146_13187.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___146_13187.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___146_13187.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___146_13187.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___146_13187.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___146_13187.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___146_13187.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___146_13187.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___146_13187.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___146_13187.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___146_13187.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___146_13187.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___146_13187.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___146_13187.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___146_13187.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___146_13187.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___146_13187.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___146_13187.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___146_13187.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___146_13187.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___146_13187.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___146_13187.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___146_13187.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___146_13187.FStar_TypeChecker_Env.dsenv})
in (

let uu____13188 = (

let uu____13199 = (

let uu____13200 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____13200 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____13199 lb))
in (match (uu____13188) with
| (e1, uu____13222, c1, g1, annotated) -> begin
(

let x = (

let uu___147_13227 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___147_13227.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___147_13227.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____13228 = (

let uu____13233 = (

let uu____13234 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____13234)::[])
in (FStar_Syntax_Subst.open_term uu____13233 e2))
in (match (uu____13228) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let uu____13253 = (

let uu____13260 = (FStar_TypeChecker_Env.push_bv env2 x1)
in (tc_term uu____13260 e21))
in (match (uu____13253) with
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

let uu____13279 = (

let uu____13282 = (

let uu____13283 = (

let uu____13296 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____13296)))
in FStar_Syntax_Syntax.Tm_let (uu____13283))
in (FStar_Syntax_Syntax.mk uu____13282))
in (uu____13279 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____13310 = (

let uu____13311 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____13312 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____13311 c1.FStar_Syntax_Syntax.res_typ uu____13312 e11)))
in (FStar_All.pipe_left (fun _0_42 -> FStar_TypeChecker_Common.NonTrivial (_0_42)) uu____13310))
in (

let g21 = (

let uu____13314 = (

let uu____13315 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____13315 g2))
in (FStar_TypeChecker_Rel.close_guard env2 xb uu____13314))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g21)
in (

let uu____13317 = (

let uu____13318 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____13318))
in (match (uu____13317) with
| true -> begin
(

let tt = (

let uu____13328 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____13328 FStar_Option.get))
in ((

let uu____13334 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____13334) with
| true -> begin
(

let uu____13335 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____13336 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____13335 uu____13336)))
end
| uu____13337 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____13338 -> begin
(

let t = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____13341 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____13341) with
| true -> begin
(

let uu____13342 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____13343 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____13342 uu____13343)))
end
| uu____13344 -> begin
()
end));
((e4), ((

let uu___148_13346 = cres
in {FStar_Syntax_Syntax.eff_name = uu___148_13346.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___148_13346.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___148_13346.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____13347 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____13379 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____13379) with
| (lbs1, e21) -> begin
(

let uu____13398 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____13398) with
| (env0, topt) -> begin
(

let uu____13417 = (build_let_rec_env true env0 lbs1)
in (match (uu____13417) with
| (lbs2, rec_env) -> begin
(

let uu____13436 = (check_let_recs rec_env lbs2)
in (match (uu____13436) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____13456 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g_lbs)
in (FStar_All.pipe_right uu____13456 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (

let uu____13462 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____13462 (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((Prims.op_Equality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
lb
end
| uu____13494 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef)
end)))))
end
| uu____13495 -> begin
(

let ecs = (

let uu____13511 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____13551 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____13551))))))
in (FStar_TypeChecker_Util.generalize env1 true uu____13511))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____13600 -> (match (uu____13600) with
| (x, uvs, e, c, gvs) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (

let uu____13647 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____13647))
in (

let uu____13652 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____13652) with
| (lbs5, e22) -> begin
((

let uu____13672 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____13672 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____13673 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____13673), (cres), (FStar_TypeChecker_Rel.trivial_guard)));
)
end))))))
end))
end))
end))
end))
end
| uu____13686 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____13718 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____13718) with
| (lbs1, e21) -> begin
(

let uu____13737 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____13737) with
| (env0, topt) -> begin
(

let uu____13756 = (build_let_rec_env false env0 lbs1)
in (match (uu____13756) with
| (lbs2, rec_env) -> begin
(

let uu____13775 = (check_let_recs rec_env lbs2)
in (match (uu____13775) with
| (lbs3, g_lbs) -> begin
(

let uu____13794 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___149_13817 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___149_13817.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___149_13817.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___150_13819 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___150_13819.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___150_13819.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___150_13819.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___150_13819.FStar_Syntax_Syntax.lbdef})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____13794) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____13846 = (tc_term env2 e21)
in (match (uu____13846) with
| (e22, cres, g2) -> begin
(

let guard = (

let uu____13863 = (

let uu____13864 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Rel.close_guard env2 uu____13864 g2))
in (FStar_TypeChecker_Rel.conj_guard g_lbs uu____13863))
in (

let cres1 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres)
in (

let tres = (norm env2 cres1.FStar_Syntax_Syntax.res_typ)
in (

let cres2 = (

let uu___151_13868 = cres1
in {FStar_Syntax_Syntax.eff_name = uu___151_13868.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___151_13868.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___151_13868.FStar_Syntax_Syntax.comp})
in (

let uu____13869 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____13869) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____13905) -> begin
((e), (cres2), (guard))
end
| FStar_Pervasives_Native.None -> begin
(

let tres1 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (

let cres3 = (

let uu___152_13910 = cres2
in {FStar_Syntax_Syntax.eff_name = uu___152_13910.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___152_13910.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___152_13910.FStar_Syntax_Syntax.comp})
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
| uu____13913 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let uu____13942 = (FStar_Options.ml_ish ())
in (match (uu____13942) with
| true -> begin
false
end
| uu____13943 -> begin
(

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____13945 = (

let uu____13950 = (

let uu____13951 = (FStar_Syntax_Subst.compress t)
in uu____13951.FStar_Syntax_Syntax.n)
in (

let uu____13954 = (

let uu____13955 = (FStar_Syntax_Subst.compress lbdef)
in uu____13955.FStar_Syntax_Syntax.n)
in ((uu____13950), (uu____13954))))
in (match (uu____13945) with
| (FStar_Syntax_Syntax.Tm_arrow (formals, c), FStar_Syntax_Syntax.Tm_abs (actuals, uu____13961, uu____13962)) -> begin
(

let actuals1 = (

let uu____14000 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____14000 actuals))
in ((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____14020 -> begin
(

let uu____14021 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____14021))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____14038 -> begin
(

let uu____14039 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____14039))
end))
in (

let msg = (

let uu____14047 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____14048 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____14047 uu____14048 formals_msg actuals_msg)))
in (FStar_Exn.raise (FStar_Errors.Error (((msg), (lbdef.FStar_Syntax_Syntax.pos))))))))
end
| uu____14049 -> begin
()
end);
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)));
))
end
| uu____14055 -> begin
(

let uu____14060 = (

let uu____14061 = (

let uu____14066 = (

let uu____14067 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____14068 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____14067 uu____14068)))
in ((uu____14066), (lbtyp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____14061))
in (FStar_Exn.raise uu____14060))
end)))
end)))
in (

let uu____14069 = (FStar_List.fold_left (fun uu____14095 lb -> (match (uu____14095) with
| (lbs1, env1) -> begin
(

let uu____14115 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____14115) with
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
| uu____14134 -> begin
(

let uu____14135 = (

let uu____14142 = (

let uu____14143 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14143))
in (tc_check_tot_or_gtot_term (

let uu___153_14154 = env0
in {FStar_TypeChecker_Env.solver = uu___153_14154.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___153_14154.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___153_14154.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___153_14154.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___153_14154.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___153_14154.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___153_14154.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___153_14154.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___153_14154.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___153_14154.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___153_14154.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___153_14154.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___153_14154.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___153_14154.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___153_14154.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___153_14154.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___153_14154.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___153_14154.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___153_14154.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___153_14154.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___153_14154.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___153_14154.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___153_14154.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___153_14154.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___153_14154.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___153_14154.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___153_14154.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___153_14154.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___153_14154.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___153_14154.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___153_14154.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___153_14154.FStar_TypeChecker_Env.dsenv}) t uu____14142))
in (match (uu____14135) with
| (t1, uu____14156, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((

let uu____14160 = (FStar_TypeChecker_Rel.discharge_guard env2 g1)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____14160));
(norm env0 t1);
))
end))
end)
in (

let env3 = (

let uu____14162 = ((termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1) && (FStar_TypeChecker_Env.should_verify env2))
in (match (uu____14162) with
| true -> begin
(

let uu___154_14163 = env2
in {FStar_TypeChecker_Env.solver = uu___154_14163.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___154_14163.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___154_14163.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___154_14163.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___154_14163.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___154_14163.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___154_14163.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___154_14163.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___154_14163.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___154_14163.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___154_14163.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___154_14163.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___154_14163.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___154_14163.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___154_14163.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___154_14163.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___154_14163.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___154_14163.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___154_14163.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___154_14163.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___154_14163.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___154_14163.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___154_14163.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___154_14163.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___154_14163.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___154_14163.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___154_14163.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___154_14163.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___154_14163.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___154_14163.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___154_14163.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___154_14163.FStar_TypeChecker_Env.dsenv})
end
| uu____14176 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname (([]), (t1)))
end))
in (

let lb1 = (

let uu___155_14180 = lb
in {FStar_Syntax_Syntax.lbname = uu___155_14180.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___155_14180.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb1)::lbs1), (env3)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____14069) with
| (lbs1, env1) -> begin
(((FStar_List.rev lbs1)), (env1))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____14203 = (

let uu____14212 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> ((

let uu____14241 = (

let uu____14242 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____14242.FStar_Syntax_Syntax.n)
in (match (uu____14241) with
| FStar_Syntax_Syntax.Tm_abs (uu____14245) -> begin
()
end
| uu____14262 -> begin
(

let uu____14263 = (

let uu____14264 = (

let uu____14269 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (("Only function literals may be defined recursively"), (uu____14269)))
in FStar_Errors.Error (uu____14264))
in (FStar_Exn.raise uu____14263))
end));
(

let uu____14270 = (

let uu____14277 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____14277 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____14270) with
| (e, c, g) -> begin
((

let uu____14286 = (

let uu____14287 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____14287)))
in (match (uu____14286) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____14288 -> begin
()
end));
(

let lb1 = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e)
in ((lb1), (g)));
)
end));
))))
in (FStar_All.pipe_right uu____14212 FStar_List.unzip))
in (match (uu____14203) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____14336 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____14336) with
| (env1, uu____14354) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____14362 = (check_lbtyp top_level env lb)
in (match (uu____14362) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (Prims.op_disEquality univ_vars1 []))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____14401 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____14406 = (tc_maybe_toplevel_term (

let uu___156_14415 = env11
in {FStar_TypeChecker_Env.solver = uu___156_14415.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___156_14415.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___156_14415.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___156_14415.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___156_14415.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___156_14415.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___156_14415.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___156_14415.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___156_14415.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___156_14415.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___156_14415.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___156_14415.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___156_14415.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___156_14415.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___156_14415.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___156_14415.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___156_14415.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___156_14415.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___156_14415.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___156_14415.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___156_14415.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___156_14415.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___156_14415.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___156_14415.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___156_14415.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___156_14415.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___156_14415.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___156_14415.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___156_14415.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___156_14415.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___156_14415.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___156_14415.FStar_TypeChecker_Env.dsenv}) e11)
in (match (uu____14406) with
| (e12, c1, g1) -> begin
(

let uu____14429 = (

let uu____14434 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____14438 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____14434 e12 c1 wf_annot))
in (match (uu____14429) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____14453 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14453) with
| true -> begin
(

let uu____14454 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____14455 = (FStar_Syntax_Print.term_to_string c11.FStar_Syntax_Syntax.res_typ)
in (

let uu____14456 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" uu____14454 uu____14455 uu____14456))))
end
| uu____14457 -> begin
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
| uu____14493 -> begin
()
end);
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____14500 -> begin
(

let uu____14501 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____14501) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____14550 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____14550)))
end
| uu____14557 -> begin
(

let uu____14558 = (FStar_Syntax_Util.type_u ())
in (match (uu____14558) with
| (k, uu____14578) -> begin
(

let uu____14579 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____14579) with
| (t2, uu____14601, g) -> begin
((

let uu____14604 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____14604) with
| true -> begin
(

let uu____14605 = (

let uu____14606 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____14606))
in (

let uu____14607 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____14605 uu____14607)))
end
| uu____14608 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____14610 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____14610))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____14618 -> (match (uu____14618) with
| (x, imp) -> begin
(

let uu____14637 = (FStar_Syntax_Util.type_u ())
in (match (uu____14637) with
| (tu, u) -> begin
((

let uu____14657 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14657) with
| true -> begin
(

let uu____14658 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14659 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14660 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____14658 uu____14659 uu____14660))))
end
| uu____14661 -> begin
()
end));
(

let uu____14662 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____14662) with
| (t, uu____14682, g) -> begin
(

let x1 = (((

let uu___157_14690 = x
in {FStar_Syntax_Syntax.ppname = uu___157_14690.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___157_14690.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____14692 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____14692) with
| true -> begin
(

let uu____14693 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____14694 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____14693 uu____14694)))
end
| uu____14695 -> begin
()
end));
(

let uu____14696 = (push_binding env x1)
in ((x1), (uu____14696), (g), (u)));
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

let uu____14786 = (tc_binder env1 b)
in (match (uu____14786) with
| (b1, env', g, u) -> begin
(

let uu____14827 = (aux env' bs2)
in (match (uu____14827) with
| (bs3, env'1, g', us) -> begin
(

let uu____14880 = (

let uu____14881 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____14881))
in (((b1)::bs3), (env'1), (uu____14880), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____14966 uu____14967 -> (match (((uu____14966), (uu____14967))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____15036 = (tc_term env1 t)
in (match (uu____15036) with
| (t1, uu____15054, g') -> begin
(

let uu____15056 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____15056)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____15098 -> (match (uu____15098) with
| (pats1, g) -> begin
(

let uu____15123 = (tc_args env p)
in (match (uu____15123) with
| (args, g') -> begin
(

let uu____15136 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats1), (uu____15136)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____15149 = (tc_maybe_toplevel_term env e)
in (match (uu____15149) with
| (e1, c, g) -> begin
(

let uu____15165 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____15165) with
| true -> begin
((e1), (c), (g))
end
| uu____15172 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (c.FStar_Syntax_Syntax.comp ())
in (

let c2 = (norm_c env c1)
in (

let uu____15178 = (

let uu____15183 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____15183) with
| true -> begin
(

let uu____15188 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____15188), (false)))
end
| uu____15189 -> begin
(

let uu____15190 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____15190), (true)))
end))
in (match (uu____15178) with
| (target_comp, allow_ghost) -> begin
(

let uu____15199 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____15199) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____15209 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in ((e1), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (uu____15209)))
end
| uu____15210 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____15219 = (

let uu____15220 = (

let uu____15225 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in ((uu____15225), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____15220))
in (FStar_Exn.raise uu____15219))
end
| uu____15232 -> begin
(

let uu____15233 = (

let uu____15234 = (

let uu____15239 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in ((uu____15239), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____15234))
in (FStar_Exn.raise uu____15233))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____15258 = (tc_tot_or_gtot_term env t)
in (match (uu____15258) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____15288 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____15288) with
| true -> begin
(

let uu____15289 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____15289))
end
| uu____15290 -> begin
()
end));
(

let env1 = (

let uu___158_15292 = env
in {FStar_TypeChecker_Env.solver = uu___158_15292.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___158_15292.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___158_15292.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___158_15292.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___158_15292.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___158_15292.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___158_15292.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___158_15292.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___158_15292.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___158_15292.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___158_15292.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___158_15292.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___158_15292.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___158_15292.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___158_15292.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___158_15292.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___158_15292.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___158_15292.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___158_15292.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___158_15292.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___158_15292.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___158_15292.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___158_15292.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___158_15292.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___158_15292.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___158_15292.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___158_15292.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___158_15292.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___158_15292.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___158_15292.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___158_15292.FStar_TypeChecker_Env.dsenv})
in (

let uu____15297 = (FStar_All.try_with (fun uu___160_15311 -> (match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)) (fun uu___159_15322 -> (match (uu___159_15322) with
| FStar_Errors.Error (msg, uu____15330) -> begin
(

let uu____15331 = (

let uu____15332 = (

let uu____15337 = (FStar_TypeChecker_Env.get_range env1)
in (((Prims.strcat "Implicit argument: " msg)), (uu____15337)))
in FStar_Errors.Error (uu____15332))
in (FStar_Exn.raise uu____15331))
end)))
in (match (uu____15297) with
| (t, c, g) -> begin
(

let uu____15353 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____15353) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____15362 -> begin
(

let uu____15363 = (

let uu____15364 = (

let uu____15369 = (

let uu____15370 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____15370))
in (

let uu____15371 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____15369), (uu____15371))))
in FStar_Errors.Error (uu____15364))
in (FStar_Exn.raise uu____15363))
end))
end)));
))


let level_of_type_fail : 'Auu____15386 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  'Auu____15386 = (fun env e t -> (

let uu____15399 = (

let uu____15400 = (

let uu____15405 = (

let uu____15406 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____15406 t))
in (

let uu____15407 = (FStar_TypeChecker_Env.get_range env)
in ((uu____15405), (uu____15407))))
in FStar_Errors.Error (uu____15400))
in (FStar_Exn.raise uu____15399)))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____15427 = (

let uu____15428 = (FStar_Syntax_Util.unrefine t1)
in uu____15428.FStar_Syntax_Syntax.n)
in (match (uu____15427) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____15432 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____15434 -> begin
(

let uu____15435 = (FStar_Syntax_Util.type_u ())
in (match (uu____15435) with
| (t_u, u) -> begin
(

let env1 = (

let uu___161_15443 = env
in {FStar_TypeChecker_Env.solver = uu___161_15443.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___161_15443.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___161_15443.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___161_15443.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___161_15443.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___161_15443.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___161_15443.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___161_15443.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___161_15443.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___161_15443.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___161_15443.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___161_15443.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___161_15443.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___161_15443.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___161_15443.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___161_15443.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___161_15443.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___161_15443.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___161_15443.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___161_15443.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___161_15443.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___161_15443.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___161_15443.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___161_15443.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___161_15443.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___161_15443.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___161_15443.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___161_15443.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___161_15443.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___161_15443.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___161_15443.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___161_15443.FStar_TypeChecker_Env.dsenv})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____15447 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____15447))
end
| uu____15448 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____15459 = (

let uu____15460 = (FStar_Syntax_Subst.compress e)
in uu____15460.FStar_Syntax_Syntax.n)
in (match (uu____15459) with
| FStar_Syntax_Syntax.Tm_bvar (uu____15465) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____15470) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____15497) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____15513) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____15536, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____15563) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____15570 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____15570) with
| ((uu____15581, t), uu____15583) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____15588, (FStar_Util.Inl (t), uu____15590), uu____15591) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____15638, (FStar_Util.Inr (c), uu____15640), uu____15641) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____15691; FStar_Syntax_Syntax.vars = uu____15692}, us) -> begin
(

let uu____15698 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____15698) with
| ((us', t), uu____15711) -> begin
((match ((Prims.op_disEquality (FStar_List.length us) (FStar_List.length us'))) with
| true -> begin
(

let uu____15717 = (

let uu____15718 = (

let uu____15723 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____15723)))
in FStar_Errors.Error (uu____15718))
in (FStar_Exn.raise uu____15717))
end
| uu____15724 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____15739 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____15740) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____15750) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____15773 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____15773) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____15793 -> (match (uu____15793) with
| (b, uu____15799) -> begin
(

let uu____15800 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____15800))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____15805 = (universe_of_aux env res)
in (level_of_type env res uu____15805)))
in (

let u_c = (

let uu____15807 = (FStar_TypeChecker_Env.effect_repr env c1 u_res)
in (match (uu____15807) with
| FStar_Pervasives_Native.None -> begin
u_res
end
| FStar_Pervasives_Native.Some (trepr) -> begin
(

let uu____15811 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____15811))
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
| FStar_Syntax_Syntax.Tm_bvar (uu____15904) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____15919) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____15958) -> begin
(

let uu____15959 = (universe_of_aux env hd3)
in ((uu____15959), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____15972) -> begin
(

let uu____15973 = (universe_of_aux env hd3)
in ((uu____15973), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____15986) -> begin
(

let uu____16003 = (universe_of_aux env hd3)
in ((uu____16003), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____16016) -> begin
(

let uu____16023 = (universe_of_aux env hd3)
in ((uu____16023), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____16036) -> begin
(

let uu____16063 = (universe_of_aux env hd3)
in ((uu____16063), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____16076) -> begin
(

let uu____16083 = (universe_of_aux env hd3)
in ((uu____16083), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____16096) -> begin
(

let uu____16097 = (universe_of_aux env hd3)
in ((uu____16097), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____16110) -> begin
(

let uu____16123 = (universe_of_aux env hd3)
in ((uu____16123), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____16136) -> begin
(

let uu____16143 = (universe_of_aux env hd3)
in ((uu____16143), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____16156) -> begin
(

let uu____16157 = (universe_of_aux env hd3)
in ((uu____16157), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____16170, (hd4)::uu____16172) -> begin
(

let uu____16237 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____16237) with
| (uu____16252, uu____16253, hd5) -> begin
(

let uu____16271 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____16271) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____16322 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____16324 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____16324) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____16375 -> begin
(

let uu____16376 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____16376) with
| (env1, uu____16398) -> begin
(

let env2 = (

let uu___162_16404 = env1
in {FStar_TypeChecker_Env.solver = uu___162_16404.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___162_16404.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___162_16404.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___162_16404.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___162_16404.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___162_16404.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___162_16404.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___162_16404.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___162_16404.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___162_16404.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___162_16404.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___162_16404.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___162_16404.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___162_16404.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___162_16404.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___162_16404.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___162_16404.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___162_16404.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___162_16404.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___162_16404.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___162_16404.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___162_16404.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___162_16404.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___162_16404.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___162_16404.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___162_16404.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___162_16404.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___162_16404.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___162_16404.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___162_16404.FStar_TypeChecker_Env.dsenv})
in ((

let uu____16406 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____16406) with
| true -> begin
(

let uu____16407 = (

let uu____16408 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____16408))
in (

let uu____16409 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____16407 uu____16409)))
end
| uu____16410 -> begin
()
end));
(

let uu____16411 = (tc_term env2 hd3)
in (match (uu____16411) with
| (uu____16432, {FStar_Syntax_Syntax.eff_name = uu____16433; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____16435; FStar_Syntax_Syntax.comp = uu____16436}, g) -> begin
((

let uu____16447 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____16447 FStar_Pervasives.ignore));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____16458 = (type_of_head true hd1 args)
in (match (uu____16458) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____16498 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____16498) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____16541 -> begin
(

let uu____16542 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____16542))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____16545, (hd1)::uu____16547) -> begin
(

let uu____16612 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____16612) with
| (uu____16615, uu____16616, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____16634, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____16679 = (universe_of_aux env e)
in (level_of_type env e uu____16679)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____16700 = (tc_binders env tps)
in (match (uu____16700) with
| (tps1, env1, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
((tps1), (env1), (us));
)
end)))




