
open Prims

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___86_4 = env
in {FStar_TypeChecker_Env.solver = uu___86_4.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___86_4.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___86_4.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___86_4.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___86_4.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___86_4.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___86_4.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___86_4.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___86_4.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___86_4.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___86_4.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___86_4.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___86_4.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___86_4.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___86_4.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___86_4.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___86_4.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___86_4.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___86_4.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___86_4.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___86_4.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___86_4.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___86_4.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___87_8 = env
in {FStar_TypeChecker_Env.solver = uu___87_8.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___87_8.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___87_8.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___87_8.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___87_8.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___87_8.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___87_8.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___87_8.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___87_8.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___87_8.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___87_8.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___87_8.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___87_8.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___87_8.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___87_8.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___87_8.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___87_8.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___87_8.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___87_8.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___87_8.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___87_8.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___87_8.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___87_8.FStar_TypeChecker_Env.qname_and_index}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v1 tl1 -> (

let r = (match ((tl1.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
| true -> begin
v1.FStar_Syntax_Syntax.pos
end
| uu____33 -> begin
(FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos tl1.FStar_Syntax_Syntax.pos)
end)
in (

let uu____34 = (

let uu____35 = (

let uu____36 = (FStar_Syntax_Syntax.as_arg v1)
in (

let uu____37 = (

let uu____39 = (FStar_Syntax_Syntax.as_arg tl1)
in (uu____39)::[])
in (uu____36)::uu____37))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____35))
in (uu____34 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun uu___80_47 -> (match (uu___80_47) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____49 -> begin
false
end))


let steps = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[])


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
t
end
| uu____100 -> begin
(

let t1 = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____103 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t1)
in (

let uu____106 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____106) with
| None -> begin
t1
end
| Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t1)
end
| uu____110 -> begin
(

let fail = (fun uu____114 -> (

let msg = (match (head_opt) with
| None -> begin
(

let uu____116 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" uu____116))
end
| Some (head1) -> begin
(

let uu____118 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____119 = (FStar_TypeChecker_Normalize.term_to_string env head1)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" uu____118 uu____119)))
end)
in (

let uu____120 = (

let uu____121 = (

let uu____124 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____124)))
in FStar_Errors.Error (uu____121))
in (Prims.raise uu____120))))
in (

let s = (

let uu____126 = (

let uu____127 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst uu____127))
in (FStar_TypeChecker_Util.new_uvar env uu____126))
in (

let uu____132 = (FStar_TypeChecker_Rel.try_teq true env t1 s)
in (match (uu____132) with
| Some (g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
s;
)
end
| uu____136 -> begin
(fail ())
end))))
end)
end))))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v1 -> (

let uu____167 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____167) with
| true -> begin
s
end
| uu____168 -> begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v1))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let uu___88_181 = lc
in {FStar_Syntax_Syntax.eff_name = uu___88_181.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___88_181.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____182 -> (

let uu____183 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ uu____183 t)))}))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> ((FStar_ST.write e.FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)));
e;
))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (

let uu____222 = (

let uu____223 = (FStar_Syntax_Subst.compress t)
in uu____223.FStar_Syntax_Syntax.n)
in (match (uu____222) with
| FStar_Syntax_Syntax.Tm_arrow (uu____226, c) -> begin
(

let uu____238 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c))
in (match (uu____238) with
| true -> begin
(

let t1 = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (

let uu____240 = (

let uu____241 = (FStar_Syntax_Subst.compress t1)
in uu____241.FStar_Syntax_Syntax.n)
in (match (uu____240) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____245) -> begin
false
end
| uu____246 -> begin
true
end)))
end
| uu____247 -> begin
false
end))
end
| uu____248 -> begin
true
end)))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____251 = (

let uu____254 = ((

let uu____255 = (should_return t)
in (not (uu____255))) || (

let uu____256 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____256))))
in (match (uu____254) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____259 -> begin
(FStar_TypeChecker_Util.return_value env t e)
end))
in (FStar_Syntax_Util.lcomp_of_comp uu____251))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____264 = (

let uu____268 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____268) with
| None -> begin
(

let uu____273 = (memo_tk e t)
in ((uu____273), (lc), (guard)))
end
| Some (t') -> begin
((

let uu____276 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____276) with
| true -> begin
(

let uu____277 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____278 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" uu____277 uu____278)))
end
| uu____279 -> begin
()
end));
(

let uu____280 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____280) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____291 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____291) with
| (e2, g) -> begin
((

let uu____300 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____300) with
| true -> begin
(

let uu____301 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____302 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____303 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____304 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____301 uu____302 uu____303 uu____304)))))
end
| uu____305 -> begin
()
end));
(

let msg = (

let uu____310 = (FStar_TypeChecker_Rel.is_trivial g)
in (match (uu____310) with
| true -> begin
None
end
| uu____316 -> begin
(FStar_All.pipe_left (fun _0_28 -> Some (_0_28)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____325 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc1 g1)
in (match (uu____325) with
| (lc2, g2) -> begin
(

let uu____333 = (memo_tk e2 t')
in ((uu____333), ((set_lcomp_result lc2 t')), (g2)))
end))));
)
end)))
end));
)
end))
in (match (uu____264) with
| (e1, lc1, g) -> begin
((

let uu____341 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____341) with
| true -> begin
(

let uu____342 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (FStar_Util.print1 "Return comp type is %s\n" uu____342))
end
| uu____343 -> begin
()
end));
((e1), (lc1), (g));
)
end))))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____359 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____359) with
| None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (t) -> begin
(

let uu____365 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____365) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt uu____387 -> (match (uu____387) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (uu____402) -> begin
copt
end
| None -> begin
(

let uu____403 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____404 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____404)))))
in (match (uu____403) with
| true -> begin
(

let uu____406 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (uu____406))
end
| uu____407 -> begin
(

let uu____408 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____408) with
| true -> begin
None
end
| uu____410 -> begin
(

let uu____411 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____411) with
| true -> begin
(

let uu____413 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (uu____413))
end
| uu____414 -> begin
(

let uu____415 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____415) with
| true -> begin
(

let uu____417 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (uu____417))
end
| uu____418 -> begin
None
end))
end))
end))
end))
end)
in (match (expected_c_opt) with
| None -> begin
(

let uu____422 = (norm_c env c)
in ((e), (uu____422), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
((

let uu____425 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____425) with
| true -> begin
(

let uu____426 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____427 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____428 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" uu____426 uu____427 uu____428))))
end
| uu____429 -> begin
()
end));
(

let c1 = (norm_c env c)
in ((

let uu____432 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____432) with
| true -> begin
(

let uu____433 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____434 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____435 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" uu____433 uu____434 uu____435))))
end
| uu____436 -> begin
()
end));
(

let uu____437 = (FStar_TypeChecker_Util.check_comp env e c1 expected_c)
in (match (uu____437) with
| (e1, uu____445, g) -> begin
(

let g1 = (

let uu____448 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____448 "could not prove post-condition" g))
in ((

let uu____450 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____450) with
| true -> begin
(

let uu____451 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____452 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" uu____451 uu____452)))
end
| uu____453 -> begin
()
end));
(

let e2 = (FStar_TypeChecker_Util.maybe_lift env e1 (FStar_Syntax_Util.comp_effect_name c1) (FStar_Syntax_Util.comp_effect_name expected_c) (FStar_Syntax_Util.comp_result c1))
in ((e2), (expected_c), (g1)));
))
end));
));
)
end))
end))


let no_logical_guard = (fun env uu____474 -> (match (uu____474) with
| (te, kt, f) -> begin
(

let uu____481 = (FStar_TypeChecker_Rel.guard_form f)
in (match (uu____481) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____486 = (

let uu____487 = (

let uu____490 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____491 = (FStar_TypeChecker_Env.get_range env)
in ((uu____490), (uu____491))))
in FStar_Errors.Error (uu____487))
in (Prims.raise uu____486))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let uu____498 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____498) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(

let uu____501 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____501))
end)))


let check_smt_pat = (fun env t bs c -> (

let uu____536 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____536) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____537; FStar_Syntax_Syntax.effect_name = uu____538; FStar_Syntax_Syntax.result_typ = uu____539; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____543))::[]; FStar_Syntax_Syntax.flags = uu____544}) -> begin
(

let pat_vars = (

let uu____578 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names uu____578))
in (

let uu____579 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____591 -> (match (uu____591) with
| (b, uu____595) -> begin
(

let uu____596 = (FStar_Util.set_mem b pat_vars)
in (not (uu____596)))
end))))
in (match (uu____579) with
| None -> begin
()
end
| Some (x, uu____600) -> begin
(

let uu____603 = (

let uu____604 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____604))
in (FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____603))
end)))
end
| uu____605 -> begin
(failwith "Impossible")
end)
end
| uu____606 -> begin
()
end)))


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (

let uu____626 = (

let uu____627 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____627)))
in (match (uu____626) with
| true -> begin
env.FStar_TypeChecker_Env.letrecs
end
| uu____631 -> begin
(match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env1 = (

let uu___89_645 = env
in {FStar_TypeChecker_Env.solver = uu___89_645.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___89_645.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___89_645.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___89_645.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___89_645.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___89_645.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___89_645.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___89_645.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___89_645.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___89_645.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___89_645.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___89_645.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___89_645.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___89_645.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___89_645.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___89_645.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___89_645.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___89_645.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___89_645.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___89_645.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___89_645.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___89_645.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___89_645.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____668 -> (match (uu____668) with
| (b, uu____673) -> begin
(

let t = (

let uu____675 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env1 uu____675))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| uu____679 -> begin
(

let uu____680 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____680)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____685 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____685) with
| (head1, uu____696) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| uu____712 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____715 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___81_719 -> (match (uu___81_719) with
| FStar_Syntax_Syntax.DECREASES (uu____720) -> begin
true
end
| uu____723 -> begin
false
end))))
in (match (uu____715) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____727 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____733 -> begin
(mk_lex_list xs)
end))
end))))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____745 -> (match (uu____745) with
| (l, t) -> begin
(

let uu____754 = (

let uu____755 = (FStar_Syntax_Subst.compress t)
in uu____755.FStar_Syntax_Syntax.n)
in (match (uu____754) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____788 -> (match (uu____788) with
| (x, imp) -> begin
(

let uu____795 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____795) with
| true -> begin
(

let uu____798 = (

let uu____799 = (

let uu____801 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (uu____801))
in (FStar_Syntax_Syntax.new_bv uu____799 x.FStar_Syntax_Syntax.sort))
in ((uu____798), (imp)))
end
| uu____802 -> begin
((x), (imp))
end))
end))))
in (

let uu____803 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____803) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____816 = (

let uu____817 = (

let uu____818 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____819 = (

let uu____821 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____821)::[])
in (uu____818)::uu____819))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____817))
in (uu____816 None r))
in (

let uu____826 = (FStar_Util.prefix formals2)
in (match (uu____826) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___90_852 = last1
in (

let uu____853 = (FStar_Syntax_Util.refine last1 precedes1)
in {FStar_Syntax_Syntax.ppname = uu___90_852.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___90_852.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____853}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____870 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____870) with
| true -> begin
(

let uu____871 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____872 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____873 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____871 uu____872 uu____873))))
end
| uu____874 -> begin
()
end));
((l), (t'));
))))
end))))
end)))
end
| uu____877 -> begin
(Prims.raise (FStar_Errors.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let uu___91_1149 = env
in {FStar_TypeChecker_Env.solver = uu___91_1149.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___91_1149.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___91_1149.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___91_1149.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___91_1149.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___91_1149.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___91_1149.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___91_1149.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___91_1149.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___91_1149.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___91_1149.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___91_1149.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___91_1149.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___91_1149.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___91_1149.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___91_1149.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___91_1149.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___91_1149.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___91_1149.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___91_1149.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___91_1149.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___91_1149.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___91_1149.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (match ((e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____1156 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____1158 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1158) with
| true -> begin
(

let uu____1159 = (

let uu____1160 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1160))
in (

let uu____1161 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" uu____1159 uu____1161)))
end
| uu____1162 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1167) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____1206 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____1206) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___92_1217 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___92_1217.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___92_1217.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___92_1217.FStar_TypeChecker_Env.implicits})
in ((e2), (c), (g1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____1230 = (FStar_Syntax_Util.type_u ())
in (match (uu____1230) with
| (t, u) -> begin
(

let uu____1238 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____1238) with
| (e2, c, g) -> begin
(

let uu____1248 = (

let uu____1257 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____1257) with
| (env2, uu____1270) -> begin
(tc_pats env2 pats)
end))
in (match (uu____1248) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___93_1291 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___93_1291.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___93_1291.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___93_1291.FStar_TypeChecker_Env.implicits})
in (

let uu____1292 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1)))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____1303 = (FStar_TypeChecker_Rel.conj_guard g g'1)
in ((uu____1292), (c), (uu____1303)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____1311 = (

let uu____1312 = (FStar_Syntax_Subst.compress e1)
in uu____1312.FStar_Syntax_Syntax.n)
in (match (uu____1311) with
| FStar_Syntax_Syntax.Tm_let ((uu____1318, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____1320; FStar_Syntax_Syntax.lbtyp = uu____1321; FStar_Syntax_Syntax.lbeff = uu____1322; FStar_Syntax_Syntax.lbdef = e11})::[]), e2) -> begin
(

let uu____1340 = (

let uu____1344 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_TypeChecker_Common.t_unit)
in (tc_term uu____1344 e11))
in (match (uu____1340) with
| (e12, c1, g1) -> begin
(

let uu____1351 = (tc_term env1 e2)
in (match (uu____1351) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e12.FStar_Syntax_Syntax.pos env1 (Some (e12)) c1 ((None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e3 = (

let uu____1368 = (

let uu____1371 = (

let uu____1372 = (

let uu____1380 = (

let uu____1384 = (

let uu____1386 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e13)))
in (uu____1386)::[])
in ((false), (uu____1384)))
in ((uu____1380), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____1372))
in (FStar_Syntax_Syntax.mk uu____1371))
in (uu____1368 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____1416 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e5), (c), (uu____1416)))))))))
end))
end))
end
| uu____1419 -> begin
(

let uu____1420 = (tc_term env1 e1)
in (match (uu____1420) with
| (e2, c, g) -> begin
(

let e3 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____1444)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____1459 = (tc_term env1 e1)
in (match (uu____1459) with
| (e2, c, g) -> begin
(

let e3 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____1485) -> begin
(

let uu____1521 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____1521) with
| (env0, uu____1529) -> begin
(

let uu____1532 = (tc_comp env0 expected_c)
in (match (uu____1532) with
| (expected_c1, uu____1540, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c1)
in (

let uu____1545 = (

let uu____1549 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____1549 e1))
in (match (uu____1545) with
| (e2, c', g') -> begin
(

let uu____1556 = (

let uu____1560 = (

let uu____1563 = (c'.FStar_Syntax_Syntax.comp ())
in ((e2), (uu____1563)))
in (check_expected_effect env0 (Some (expected_c1)) uu____1560))
in (match (uu____1556) with
| (e3, expected_c2, g'') -> begin
(

let e4 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (t_res)), (None))), (Some ((FStar_Syntax_Util.comp_effect_name expected_c2))))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____1614 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____1614))
in (

let topt1 = (tc_tactic_opt env0 topt)
in (

let f1 = (match (topt1) with
| None -> begin
f
end
| Some (tactic) -> begin
(FStar_TypeChecker_Rel.map_guard f (FStar_TypeChecker_Common.mk_by_tactic tactic))
end)
in (

let uu____1619 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____1619) with
| (e5, c, f2) -> begin
(

let uu____1629 = (FStar_TypeChecker_Rel.conj_guard f1 f2)
in ((e5), (c), (uu____1629)))
end)))))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____1633) -> begin
(

let uu____1669 = (FStar_Syntax_Util.type_u ())
in (match (uu____1669) with
| (k, u) -> begin
(

let uu____1677 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____1677) with
| (t1, uu____1685, f) -> begin
(

let uu____1687 = (

let uu____1691 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____1691 e1))
in (match (uu____1687) with
| (e2, c, g) -> begin
(

let uu____1698 = (

let uu____1701 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____1704 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____1701 e2 c f))
in (match (uu____1698) with
| (c1, f1) -> begin
(

let uu____1710 = (

let uu____1714 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (None))), (Some (c1.FStar_Syntax_Syntax.eff_name)))))) (Some (t1.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____1714 c1))
in (match (uu____1710) with
| (e3, c2, f2) -> begin
(

let uu____1750 = (

let uu____1751 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____1751))
in ((e3), (c2), (uu____1750)))
end))
end))
end))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd1)::rest)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_)); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd1)::rest)) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____1828 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1828) with
| (unary_op, uu____1842) -> begin
(

let head1 = (

let uu____1860 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[]))))) None uu____1860))
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1))))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____1904; FStar_Syntax_Syntax.pos = uu____1905; FStar_Syntax_Syntax.vars = uu____1906}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____1931 -> begin
()
end);
(

let uu____1932 = (

let uu____1936 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____1936) with
| (env0, uu____1944) -> begin
(tc_term env0 e1)
end))
in (match (uu____1932) with
| (e2, c, g) -> begin
(

let uu____1953 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1953) with
| (reify_op, uu____1967) -> begin
(

let u_c = (

let uu____1983 = (tc_term env1 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____1983) with
| (uu____1987, c', uu____1989) -> begin
(

let uu____1990 = (

let uu____1991 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____1991.FStar_Syntax_Syntax.n)
in (match (uu____1990) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____1995 -> begin
(

let uu____1996 = (FStar_Syntax_Util.type_u ())
in (match (uu____1996) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| None -> begin
(

let uu____2005 = (

let uu____2006 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____2007 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____2008 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____2006 uu____2007 uu____2008))))
in (failwith uu____2005))
end);
u;
))
end))
end))
end))
in (

let repr = (

let uu____2010 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_TypeChecker_Env.reify_comp env1 uu____2010 u_c))
in (

let e3 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[]))))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____2032 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____2032 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____2033 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____2033) with
| (e4, c2, g') -> begin
(

let uu____2043 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e4), (c2), (uu____2043)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = uu____2045; FStar_Syntax_Syntax.pos = uu____2046; FStar_Syntax_Syntax.vars = uu____2047}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____2072 -> begin
()
end);
(

let no_reflect = (fun uu____2079 -> (

let uu____2080 = (

let uu____2081 = (

let uu____2084 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((uu____2084), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____2081))
in (Prims.raise uu____2080)))
in (

let uu____2088 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2088) with
| (reflect_op, uu____2102) -> begin
(

let uu____2117 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____2117) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
(

let uu____2123 = (

let uu____2124 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____2124)))
in (match (uu____2123) with
| true -> begin
(no_reflect ())
end
| uu____2129 -> begin
(

let uu____2130 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2130) with
| (env_no_ex, topt) -> begin
(

let uu____2141 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____2156 = (

let uu____2159 = (

let uu____2160 = (

let uu____2170 = (

let uu____2172 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____2173 = (

let uu____2175 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____2175)::[])
in (uu____2172)::uu____2173))
in ((repr), (uu____2170)))
in FStar_Syntax_Syntax.Tm_app (uu____2160))
in (FStar_Syntax_Syntax.mk uu____2159))
in (uu____2156 None top.FStar_Syntax_Syntax.pos))
in (

let uu____2185 = (

let uu____2189 = (

let uu____2190 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____2190 Prims.fst))
in (tc_tot_or_gtot_term uu____2189 t))
in (match (uu____2185) with
| (t1, uu____2207, g) -> begin
(

let uu____2209 = (

let uu____2210 = (FStar_Syntax_Subst.compress t1)
in uu____2210.FStar_Syntax_Syntax.n)
in (match (uu____2209) with
| FStar_Syntax_Syntax.Tm_app (uu____2221, ((res, uu____2223))::((wp, uu____2225))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____2259 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____2141) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____2283 = (

let uu____2286 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____2286) with
| (e2, c, g) -> begin
((

let uu____2296 = (

let uu____2297 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____2297))
in (match (uu____2296) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 (((("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____2302 -> begin
()
end));
(

let uu____2303 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____2303) with
| None -> begin
((

let uu____2308 = (

let uu____2312 = (

let uu____2315 = (

let uu____2316 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2317 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____2316 uu____2317)))
in ((uu____2315), (e2.FStar_Syntax_Syntax.pos)))
in (uu____2312)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____2308));
(

let uu____2322 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e2), (uu____2322)));
)
end
| Some (g') -> begin
(

let uu____2324 = (

let uu____2325 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____2325))
in ((e2), (uu____2324)))
end));
)
end))
in (match (uu____2283) with
| (e2, g) -> begin
(

let c = (

let uu____2332 = (

let uu____2333 = (

let uu____2334 = (

let uu____2335 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____2335)::[])
in (

let uu____2336 = (

let uu____2342 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2342)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____2334; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____2336; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____2333))
in (FStar_All.pipe_right uu____2332 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[]))))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____2363 = (comp_check_expected_typ env1 e3 c)
in (match (uu____2363) with
| (e4, c1, g') -> begin
(

let uu____2373 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e4), (c1), (uu____2373)))
end))))
end))
end))
end))
end))
end))
end)));
)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let env0 = env1
in (

let env2 = (

let uu____2392 = (

let uu____2393 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____2393 Prims.fst))
in (FStar_All.pipe_right uu____2392 instantiate_both))
in ((

let uu____2402 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____2402) with
| true -> begin
(

let uu____2403 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____2404 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____2403 uu____2404)))
end
| uu____2405 -> begin
()
end));
(

let uu____2406 = (tc_term (no_inst env2) head1)
in (match (uu____2406) with
| (head2, chead, g_head) -> begin
(

let uu____2416 = (

let uu____2420 = ((not (env2.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____2420) with
| true -> begin
(

let uu____2424 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____2424))
end
| uu____2426 -> begin
(

let uu____2427 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env2 head2 chead g_head args uu____2427))
end))
in (match (uu____2416) with
| (e1, c, g) -> begin
((

let uu____2436 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____2436) with
| true -> begin
(

let uu____2437 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____2437))
end
| uu____2438 -> begin
()
end));
(

let c1 = (

let uu____2440 = (((FStar_TypeChecker_Env.should_verify env2) && (

let uu____2441 = (FStar_Syntax_Util.is_lcomp_partial_return c)
in (not (uu____2441)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____2440) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e1 c)
end
| uu____2442 -> begin
c
end))
in (

let uu____2443 = (comp_check_expected_typ env0 e1 c1)
in (match (uu____2443) with
| (e2, c2, g') -> begin
(

let gimp = (

let uu____2454 = (

let uu____2455 = (FStar_Syntax_Subst.compress head2)
in uu____2455.FStar_Syntax_Syntax.n)
in (match (uu____2454) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____2459) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e2), (c2.FStar_Syntax_Syntax.res_typ), (head2.FStar_Syntax_Syntax.pos))
in (

let uu___94_2491 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___94_2491.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___94_2491.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___94_2491.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____2516 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (

let uu____2518 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g uu____2518))
in ((

let uu____2520 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____2520) with
| true -> begin
(

let uu____2521 = (FStar_Syntax_Print.term_to_string e2)
in (

let uu____2522 = (FStar_TypeChecker_Rel.guard_to_string env2 gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____2521 uu____2522)))
end
| uu____2523 -> begin
()
end));
((e2), (c2), (gres));
)))
end)));
)
end))
end));
)))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let uu____2552 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2552) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____2564 = (tc_term env12 e1)
in (match (uu____2564) with
| (e11, c1, g1) -> begin
(

let uu____2574 = (match (topt) with
| Some (t) -> begin
((env1), (t))
end
| None -> begin
(

let uu____2580 = (FStar_Syntax_Util.type_u ())
in (match (uu____2580) with
| (k, uu____2586) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env1 k)
in (

let uu____2588 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in ((uu____2588), (res_t))))
end))
end)
in (match (uu____2574) with
| (env_branches, res_t) -> begin
((

let uu____2595 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____2595) with
| true -> begin
(

let uu____2596 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____2596))
end
| uu____2597 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____2647 = (

let uu____2650 = (FStar_List.fold_right (fun uu____2669 uu____2670 -> (match (((uu____2669), (uu____2670))) with
| ((uu____2702, f, c, g), (caccum, gaccum)) -> begin
(

let uu____2735 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (uu____2735)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____2650) with
| (cases, g) -> begin
(

let uu____2756 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____2756), (g)))
end))
in (match (uu____2647) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (Some (e11)) c1 ((Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____2809 -> (match (uu____2809) with
| ((pat, wopt, br), uu____2825, lc, uu____2827) -> begin
(

let uu____2834 = (FStar_TypeChecker_Util.maybe_lift env1 br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (uu____2834)))
end))))
in (

let e2 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (None))), (Some (cres.FStar_Syntax_Syntax.eff_name)))))) None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____2890 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____2890) with
| true -> begin
(mk_match e11)
end
| uu____2893 -> begin
(

let e_match = (

let uu____2897 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____2897))
in (

let lb = (

let uu____2901 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = uu____2901; FStar_Syntax_Syntax.lbdef = e11})
in (

let e2 = (

let uu____2905 = (

let uu____2908 = (

let uu____2909 = (

let uu____2917 = (

let uu____2918 = (

let uu____2919 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____2919)::[])
in (FStar_Syntax_Subst.close uu____2918 e_match))
in ((((false), ((lb)::[]))), (uu____2917)))
in FStar_Syntax_Syntax.Tm_let (uu____2909))
in (FStar_Syntax_Syntax.mk uu____2908))
in (uu____2905 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____2933 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____2933) with
| true -> begin
(

let uu____2934 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____2935 = (

let uu____2936 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2936))
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____2934 uu____2935)))
end
| uu____2937 -> begin
()
end));
(

let uu____2938 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e2), (cres), (uu____2938)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2941); FStar_Syntax_Syntax.lbunivs = uu____2942; FStar_Syntax_Syntax.lbtyp = uu____2943; FStar_Syntax_Syntax.lbeff = uu____2944; FStar_Syntax_Syntax.lbdef = uu____2945})::[]), uu____2946) -> begin
((

let uu____2961 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____2961) with
| true -> begin
(

let uu____2962 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____2962))
end
| uu____2963 -> begin
()
end));
(check_top_level_let env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____2964), uu____2965) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2975); FStar_Syntax_Syntax.lbunivs = uu____2976; FStar_Syntax_Syntax.lbtyp = uu____2977; FStar_Syntax_Syntax.lbeff = uu____2978; FStar_Syntax_Syntax.lbdef = uu____2979})::uu____2980), uu____2981) -> begin
((

let uu____2997 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____2997) with
| true -> begin
(

let uu____2998 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____2998))
end
| uu____2999 -> begin
()
end));
(check_top_level_let_rec env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____3000), uu____3001) -> begin
(check_inner_let_rec env1 top)
end));
)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option  ->  FStar_Syntax_Syntax.term Prims.option = (fun env topt -> (match (topt) with
| None -> begin
None
end
| Some (tactic) -> begin
(

let uu____3024 = (tc_check_tot_or_gtot_term env tactic FStar_TypeChecker_Common.t_tactic_unit)
in (match (uu____3024) with
| (tactic1, uu____3030, uu____3031) -> begin
Some (tactic1)
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t -> (

let uu____3066 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____3066) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____3079 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____3079) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____3082 -> begin
(

let uu____3083 = (

let uu____3084 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3084))
in FStar_Util.Inr (uu____3083))
end))
in (

let is_data_ctor = (fun uu___82_3093 -> (match (uu___82_3093) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| uu____3096 -> begin
false
end))
in (

let uu____3098 = ((is_data_ctor dc) && (

let uu____3099 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____3099))))
in (match (uu____3098) with
| true -> begin
(

let uu____3105 = (

let uu____3106 = (

let uu____3109 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____3112 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____3109), (uu____3112))))
in FStar_Errors.Error (uu____3106))
in (Prims.raise uu____3105))
end
| uu____3116 -> begin
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

let uu____3123 = (

let uu____3124 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____3124))
in (failwith uu____3123))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____3143 = (

let uu____3144 = (FStar_Syntax_Subst.compress t1)
in uu____3144.FStar_Syntax_Syntax.n)
in (match (uu____3143) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3147) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____3155 -> begin
(

let imp = (("uvar in term"), (env1), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___95_3175 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___95_3175.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___95_3175.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___95_3175.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env1 e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____3203 = (

let uu____3210 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____3210) with
| None -> begin
(

let uu____3218 = (FStar_Syntax_Util.type_u ())
in (match (uu____3218) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____3203) with
| (t, uu____3239, g0) -> begin
(

let uu____3247 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____3247) with
| (e1, uu____3258, g1) -> begin
(

let uu____3266 = (

let uu____3267 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____3267 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____3268 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e1), (uu____3266), (uu____3268))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____3270 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____3279 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____3279)))
end
| uu____3282 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____3270) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___96_3293 = x
in {FStar_Syntax_Syntax.ppname = uu___96_3293.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___96_3293.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Common.insert_bv x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____3296 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____3296) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____3309 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____3309) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____3312 -> begin
(

let uu____3313 = (

let uu____3314 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3314))
in FStar_Util.Inr (uu____3313))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____3320; FStar_Syntax_Syntax.pos = uu____3321; FStar_Syntax_Syntax.vars = uu____3322}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____3330 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3330) with
| ((us', t), range) -> begin
((match (((FStar_List.length us1) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____3352 = (

let uu____3353 = (

let uu____3356 = (FStar_TypeChecker_Env.get_range env1)
in (("Unexpected number of universe instantiations"), (uu____3356)))
in FStar_Errors.Error (uu____3353))
in (Prims.raise uu____3352))
end
| uu____3357 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____3364 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (

let uu___97_3366 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___98_3367 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___98_3367.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___98_3367.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___97_3366.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___97_3366.FStar_Syntax_Syntax.fv_qual})
in (

let fv'1 = (FStar_Syntax_Syntax.set_range_of_fv fv' range)
in ((FStar_TypeChecker_Common.insert_fv fv'1 t);
(

let e1 = (

let uu____3383 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'1))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3383 us1))
in (check_instantiated_fvar env1 fv'1.FStar_Syntax_Syntax.fv_name fv'1.FStar_Syntax_Syntax.fv_qual e1 t));
)));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3395 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3395) with
| ((us, t), range) -> begin
((

let uu____3413 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____3413) with
| true -> begin
(

let uu____3414 = (

let uu____3415 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____3415))
in (

let uu____3416 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____3417 = (FStar_Range.string_of_range range)
in (

let uu____3418 = (FStar_Range.string_of_use_range range)
in (

let uu____3419 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s" uu____3414 uu____3416 uu____3417 uu____3418 uu____3419))))))
end
| uu____3420 -> begin
()
end));
(

let fv' = (

let uu___99_3422 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___100_3423 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___100_3423.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___100_3423.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___99_3422.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___99_3422.FStar_Syntax_Syntax.fv_qual})
in (

let fv'1 = (FStar_Syntax_Syntax.set_range_of_fv fv' range)
in ((FStar_TypeChecker_Common.insert_fv fv'1 t);
(

let e1 = (

let uu____3439 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'1))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3439 us))
in (check_instantiated_fvar env1 fv'1.FStar_Syntax_Syntax.fv_name fv'1.FStar_Syntax_Syntax.fv_qual e1 t));
)));
)
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (

let e1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 e1 (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3475 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3475) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____3484 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3484) with
| (env2, uu____3492) -> begin
(

let uu____3495 = (tc_binders env2 bs1)
in (match (uu____3495) with
| (bs2, env3, g, us) -> begin
(

let uu____3507 = (tc_comp env3 c1)
in (match (uu____3507) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___101_3520 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___101_3520.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___101_3520.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___101_3520.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____3541 = (FStar_TypeChecker_Rel.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Rel.conj_guard g uu____3541))
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

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u1)))) None top.FStar_Syntax_Syntax.pos)
in (

let e1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u1))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 e1 (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____3576 = (

let uu____3579 = (

let uu____3580 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3580)::[])
in (FStar_Syntax_Subst.open_term uu____3579 phi))
in (match (uu____3576) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____3587 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3587) with
| (env2, uu____3595) -> begin
(

let uu____3598 = (

let uu____3605 = (FStar_List.hd x1)
in (tc_binder env2 uu____3605))
in (match (uu____3598) with
| (x2, env3, f1, u) -> begin
((

let uu____3622 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____3622) with
| true -> begin
(

let uu____3623 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3624 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____3625 = (FStar_Syntax_Print.bv_to_string (Prims.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____3623 uu____3624 uu____3625))))
end
| uu____3626 -> begin
()
end));
(

let uu____3627 = (FStar_Syntax_Util.type_u ())
in (match (uu____3627) with
| (t_phi, uu____3634) -> begin
(

let uu____3635 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____3635) with
| (phi2, uu____3643, f2) -> begin
(

let e1 = (

let uu___102_3648 = (FStar_Syntax_Util.refine (Prims.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___102_3648.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___102_3648.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___102_3648.FStar_Syntax_Syntax.vars})
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____3667 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____3667))
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____3676) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____3701 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____3701) with
| true -> begin
(

let uu____3702 = (FStar_Syntax_Print.term_to_string (

let uu___103_3703 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (None))); FStar_Syntax_Syntax.tk = uu___103_3703.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___103_3703.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___103_3703.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____3702))
end
| uu____3721 -> begin
()
end));
(

let uu____3722 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____3722) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____3730 -> begin
(

let uu____3731 = (

let uu____3732 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____3733 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____3732 uu____3733)))
in (failwith uu____3731))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (uu____3739) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (uu____3740, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (uu____3746, Some (uu____3747)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____3755) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (uu____3759) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (uu____3760) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____3761) -> begin
FStar_TypeChecker_Common.t_range
end
| uu____3762 -> begin
(Prims.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____3773) -> begin
(

let uu____3780 = (FStar_Syntax_Util.type_u ())
in (match (uu____3780) with
| (k, u) -> begin
(

let uu____3788 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3788) with
| (t1, uu____3796, g) -> begin
(

let uu____3798 = (FStar_Syntax_Syntax.mk_Total' t1 (Some (u)))
in ((uu____3798), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____3800) -> begin
(

let uu____3807 = (FStar_Syntax_Util.type_u ())
in (match (uu____3807) with
| (k, u) -> begin
(

let uu____3815 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3815) with
| (t1, uu____3823, g) -> begin
(

let uu____3825 = (FStar_Syntax_Syntax.mk_GTotal' t1 (Some (u)))
in ((uu____3825), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let head1 = (FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let head2 = (match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
head1
end
| us -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((head1), (us))))) None c0.FStar_Syntax_Syntax.pos)
end)
in (

let tc = (

let uu____3841 = (

let uu____3842 = (

let uu____3843 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____3843)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____3842))
in (uu____3841 None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____3848 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____3848) with
| (tc1, uu____3856, f) -> begin
(

let uu____3858 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____3858) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____3888 = (

let uu____3889 = (FStar_Syntax_Subst.compress head3)
in uu____3889.FStar_Syntax_Syntax.n)
in (match (uu____3888) with
| FStar_Syntax_Syntax.Tm_uinst (uu____3892, us) -> begin
us
end
| uu____3898 -> begin
[]
end))
in (

let uu____3899 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____3899) with
| (uu____3912, args1) -> begin
(

let uu____3928 = (

let uu____3940 = (FStar_List.hd args1)
in (

let uu____3949 = (FStar_List.tl args1)
in ((uu____3940), (uu____3949))))
in (match (uu____3928) with
| (res, args2) -> begin
(

let uu____3991 = (

let uu____3996 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___83_4006 -> (match (uu___83_4006) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____4012 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____4012) with
| (env1, uu____4019) -> begin
(

let uu____4022 = (tc_tot_or_gtot_term env1 e)
in (match (uu____4022) with
| (e1, uu____4029, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____3996 FStar_List.unzip))
in (match (uu____3991) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___104_4052 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___104_4052.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___104_4052.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____4056 = (FStar_TypeChecker_Env.effect_repr env c2 u)
in (match (uu____4056) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____4059 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c2), (u_c), (uu____4059))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____4067) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____4070 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____4070))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____4073 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____4073))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u2
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____4076 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____4077 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____4077 Prims.snd))
end
| uu____4082 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (

let uu____4103 = (

let uu____4104 = (

let uu____4107 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((uu____4107), (top.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____4104))
in (Prims.raise uu____4103)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____4161 bs2 bs_expected1 -> (match (uu____4161) with
| (env2, out, g, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ((FStar_List.rev out)), (None), (g), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(

let uu____4258 = (

let uu____4259 = (

let uu____4262 = (

let uu____4263 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____4263))
in (

let uu____4264 = (FStar_Syntax_Syntax.range_of_bv hd1)
in ((uu____4262), (uu____4264))))
in FStar_Errors.Error (uu____4259))
in (Prims.raise uu____4258))
end
| uu____4265 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____4269 = (

let uu____4272 = (

let uu____4273 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____4273.FStar_Syntax_Syntax.n)
in (match (uu____4272) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____4278 -> begin
((

let uu____4280 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____4280) with
| true -> begin
(

let uu____4281 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____4281))
end
| uu____4282 -> begin
()
end));
(

let uu____4283 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____4283) with
| (t, uu____4290, g1) -> begin
(

let g2 = (

let uu____4293 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____4294 = (FStar_TypeChecker_Rel.teq env2 t expected_t)
in (FStar_TypeChecker_Util.label_guard uu____4293 "Type annotation on parameter incompatible with the expected type" uu____4294)))
in (

let g3 = (

let uu____4296 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____4296))
in ((t), (g3))))
end));
)
end))
in (match (uu____4269) with
| (t, g1) -> begin
(

let hd2 = (

let uu___105_4312 = hd1
in {FStar_Syntax_Syntax.ppname = uu___105_4312.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___105_4312.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env3 = (push_binding env2 b)
in (

let subst2 = (

let uu____4321 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____4321))
in (aux ((env3), ((b)::out), (g1), (subst2)) bs3 bs_expected2))))))
end)));
)
end
| (rest, []) -> begin
((env2), ((FStar_List.rev out)), (Some (FStar_Util.Inl (rest))), (g), (subst1))
end
| ([], rest) -> begin
((env2), ((FStar_List.rev out)), (Some (FStar_Util.Inr (rest))), (g), (subst1))
end)
end))
in (aux ((env1), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs1 bs_expected)))
in (

let rec expected_function_typ1 = (fun env1 t0 body1 -> (match (t0) with
| None -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4423 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____4427 = (tc_binders env1 bs)
in (match (uu____4427) with
| (bs1, envbody, g, uu____4448) -> begin
(

let uu____4449 = (

let uu____4456 = (

let uu____4457 = (FStar_Syntax_Subst.compress body1)
in uu____4457.FStar_Syntax_Syntax.n)
in (match (uu____4456) with
| FStar_Syntax_Syntax.Tm_ascribed (e, (FStar_Util.Inr (c), tacopt), uu____4469) -> begin
(

let uu____4505 = (tc_comp envbody c)
in (match (uu____4505) with
| (c1, uu____4516, g') -> begin
(

let uu____4518 = (tc_tactic_opt envbody tacopt)
in (

let uu____4520 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c1)), (uu____4518), (body1), (uu____4520))))
end))
end
| uu____4523 -> begin
((None), (None), (body1), (g))
end))
in (match (uu____4449) with
| (copt, tacopt, body2, g1) -> begin
((None), (bs1), ([]), (copt), (tacopt), (envbody), (body2), (g1))
end))
end));
)
end
| Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____4582 = (

let uu____4583 = (FStar_Syntax_Subst.compress t2)
in uu____4583.FStar_Syntax_Syntax.n)
in (match (uu____4582) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4616 -> begin
(failwith "Impossible")
end);
(

let uu____4620 = (tc_binders env1 bs)
in (match (uu____4620) with
| (bs1, envbody, g, uu____4642) -> begin
(

let uu____4643 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____4643) with
| (envbody1, uu____4662) -> begin
((Some (((t2), (true)))), (bs1), ([]), (None), (None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____4674) -> begin
(

let uu____4679 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____4679) with
| (uu____4708, bs1, bs', copt, tacopt, env2, body2, g) -> begin
((Some (((t2), (false)))), (bs1), (bs'), (copt), (tacopt), (env2), (body2), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____4748 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____4748) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 -> (

let rec handle_more = (fun uu____4811 c_expected2 -> (match (uu____4811) with
| (env3, bs2, more, guard, subst1) -> begin
(match (more) with
| None -> begin
(

let uu____4872 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env3), (bs2), (guard), (uu____4872)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____4889 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____4889))
in (

let uu____4890 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env3), (bs2), (guard), (uu____4890))))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (match ((FStar_Syntax_Util.is_named_tot c)) with
| true -> begin
(

let t3 = (unfold_whnf env3 (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____4931 = (check_binders env3 more_bs bs_expected3)
in (match (uu____4931) with
| (env4, bs', more1, guard', subst2) -> begin
(

let uu____4958 = (

let uu____4974 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env4), ((FStar_List.append bs2 bs')), (more1), (uu____4974), (subst2)))
in (handle_more uu____4958 c_expected3))
end))
end
| uu____4983 -> begin
(

let uu____4984 = (

let uu____4985 = (FStar_Syntax_Print.term_to_string t3)
in (FStar_Util.format1 "More arguments than annotated type (%s)" uu____4985))
in (fail uu____4984 t3))
end))
end
| uu____4993 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t2)
end))
end)
end))
in (

let uu____5001 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____5001 c_expected1))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___106_5039 = envbody
in {FStar_TypeChecker_Env.solver = uu___106_5039.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___106_5039.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___106_5039.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___106_5039.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___106_5039.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___106_5039.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___106_5039.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___106_5039.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___106_5039.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___106_5039.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___106_5039.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___106_5039.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___106_5039.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___106_5039.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___106_5039.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___106_5039.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___106_5039.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___106_5039.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___106_5039.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___106_5039.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___106_5039.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___106_5039.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___106_5039.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____5053 uu____5054 -> (match (((uu____5053), (uu____5054))) with
| ((env2, letrec_binders), (l, t3)) -> begin
(

let uu____5079 = (

let uu____5083 = (

let uu____5084 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____5084 Prims.fst))
in (tc_term uu____5083 t3))
in (match (uu____5079) with
| (t4, uu____5096, uu____5097) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l (([]), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____5104 = (FStar_Syntax_Syntax.mk_binder (

let uu___107_5105 = x
in {FStar_Syntax_Syntax.ppname = uu___107_5105.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_5105.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____5104)::letrec_binders)
end
| uu____5106 -> begin
letrec_binders
end)
in ((env3), (lb))))
end))
end)) ((envbody1), ([])))))))
in (

let uu____5109 = (check_actuals_against_formals env1 bs bs_expected1)
in (match (uu____5109) with
| (envbody, bs1, g, c) -> begin
(

let uu____5141 = (

let uu____5145 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5145) with
| true -> begin
(mk_letrec_env envbody bs1 c)
end
| uu____5149 -> begin
((envbody), ([]))
end))
in (match (uu____5141) with
| (envbody1, letrecs) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in ((Some (((t2), (false)))), (bs1), (letrecs), (Some (c)), (None), (envbody2), (body1), (g)))
end))
end))))
end))
end
| uu____5181 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____5196 = (unfold_whnf env1 t2)
in (as_function_typ true uu____5196))
end
| uu____5197 -> begin
(

let uu____5198 = (expected_function_typ1 env1 None body1)
in (match (uu____5198) with
| (uu____5226, bs1, uu____5228, c_opt, tacopt, envbody, body2, g) -> begin
((Some (((t2), (false)))), (bs1), ([]), (c_opt), (tacopt), (envbody), (body2), (g))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____5253 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____5253) with
| (env1, topt) -> begin
((

let uu____5265 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____5265) with
| true -> begin
(

let uu____5266 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____5266 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____5268 -> begin
"false"
end)))
end
| uu____5269 -> begin
()
end));
(

let uu____5270 = (expected_function_typ1 env1 topt body)
in (match (uu____5270) with
| (tfun_opt, bs1, letrec_binders, c_opt, tacopt, envbody, body1, g) -> begin
(

let uu____5305 = (tc_term (

let uu___108_5309 = envbody
in {FStar_TypeChecker_Env.solver = uu___108_5309.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___108_5309.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___108_5309.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___108_5309.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___108_5309.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___108_5309.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___108_5309.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___108_5309.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___108_5309.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___108_5309.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___108_5309.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___108_5309.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___108_5309.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___108_5309.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___108_5309.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___108_5309.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___108_5309.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___108_5309.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___108_5309.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___108_5309.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___108_5309.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___108_5309.FStar_TypeChecker_Env.qname_and_index}) body1)
in (match (uu____5305) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in ((

let uu____5318 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Implicits")))
in (match (uu____5318) with
| true -> begin
(

let uu____5319 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body1.FStar_TypeChecker_Env.implicits))
in (

let uu____5328 = (

let uu____5329 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____5329))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" uu____5319 uu____5328)))
end
| uu____5330 -> begin
()
end));
(

let uu____5331 = (

let uu____5335 = (

let uu____5338 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body2), (uu____5338)))
in (check_expected_effect (

let uu___109_5343 = envbody
in {FStar_TypeChecker_Env.solver = uu___109_5343.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___109_5343.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___109_5343.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___109_5343.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___109_5343.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___109_5343.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___109_5343.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___109_5343.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___109_5343.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___109_5343.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___109_5343.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___109_5343.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___109_5343.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___109_5343.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___109_5343.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___109_5343.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___109_5343.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___109_5343.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___109_5343.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___109_5343.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___109_5343.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___109_5343.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___109_5343.FStar_TypeChecker_Env.qname_and_index}) c_opt uu____5335))
in (match (uu____5331) with
| (body3, cbody1, guard) -> begin
(

let guard1 = (FStar_TypeChecker_Rel.conj_guard guard_body1 guard)
in (

let guard2 = (

let uu____5352 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____5353 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____5353))))
in (match (uu____5352) with
| true -> begin
(

let uu____5354 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____5354))
end
| uu____5355 -> begin
(

let guard2 = (

let uu____5357 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in (FStar_TypeChecker_Rel.close_guard env1 (FStar_List.append bs1 letrec_binders) uu____5357))
in guard2)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody1)
in (

let e = (

let uu____5364 = (

let uu____5371 = (

let uu____5377 = (FStar_All.pipe_right (FStar_Util.dflt cbody1 c_opt) FStar_Syntax_Util.lcomp_of_comp)
in (FStar_All.pipe_right uu____5377 (fun _0_29 -> FStar_Util.Inl (_0_29))))
in Some (uu____5371))
in (FStar_Syntax_Util.abs bs1 body3 uu____5364))
in (

let uu____5391 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5406) -> begin
((e), (t1), (guard2))
end
| uu____5414 -> begin
(

let uu____5415 = (match (use_teq) with
| true -> begin
(

let uu____5420 = (FStar_TypeChecker_Rel.teq env1 t1 tfun_computed)
in ((e), (uu____5420)))
end
| uu____5421 -> begin
(FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
end)
in (match (uu____5415) with
| (e1, guard') -> begin
(

let uu____5427 = (FStar_TypeChecker_Rel.conj_guard guard2 guard')
in ((e1), (t1), (uu____5427)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard2))
end)
in (match (uu____5391) with
| (e1, tfun, guard3) -> begin
(

let c = (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____5439 -> begin
(FStar_TypeChecker_Util.return_value env1 tfun e1)
end)
in (

let uu____5440 = (FStar_TypeChecker_Util.strengthen_precondition None env1 e1 (FStar_Syntax_Util.lcomp_of_comp c) guard3)
in (match (uu____5440) with
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
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head1 chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in ((

let uu____5476 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5476) with
| true -> begin
(

let uu____5477 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____5478 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____5477 uu____5478)))
end
| uu____5479 -> begin
()
end));
(

let monadic_application = (fun uu____5520 subst1 arg_comps_rev arg_rets guard fvs bs -> (match (uu____5520) with
| (head2, chead1, ghead1, cres) -> begin
(

let rt = (check_no_escape (Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres1 = (

let uu___110_5561 = cres
in {FStar_Syntax_Syntax.eff_name = uu___110_5561.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___110_5561.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___110_5561.FStar_Syntax_Syntax.comp})
in (

let uu____5562 = (match (bs) with
| [] -> begin
(

let cres2 = (FStar_TypeChecker_Util.subst_lcomp subst1 cres1)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun uu___84_5589 -> (match (uu___84_5589) with
| (uu____5598, uu____5599, FStar_Util.Inl (uu____5600)) -> begin
false
end
| (uu____5611, uu____5612, FStar_Util.Inr (c)) -> begin
(

let uu____5622 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (not (uu____5622)))
end)))))
in (

let cres3 = (match (refine_with_equality) with
| true -> begin
(

let uu____5624 = ((FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets)) (Some (cres2.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env uu____5624 cres2))
end
| uu____5633 -> begin
((

let uu____5635 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5635) with
| true -> begin
(

let uu____5636 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____5637 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (

let uu____5638 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" uu____5636 uu____5637 uu____5638))))
end
| uu____5639 -> begin
()
end));
cres2;
)
end)
in ((cres3), (g))))))
end
| uu____5640 -> begin
(

let g = (

let uu____5645 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____5645 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (

let uu____5646 = (

let uu____5647 = (

let uu____5650 = (

let uu____5651 = (

let uu____5652 = (cres1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs uu____5652))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst1) uu____5651))
in (FStar_Syntax_Syntax.mk_Total uu____5650))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5647))
in ((uu____5646), (g))))
end)
in (match (uu____5562) with
| (cres2, guard1) -> begin
((

let uu____5663 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5663) with
| true -> begin
(

let uu____5664 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____5664))
end
| uu____5665 -> begin
()
end));
(

let comp = (FStar_List.fold_left (fun out_c uu____5680 -> (match (uu____5680) with
| ((e, q), x, c) -> begin
(match (c) with
| FStar_Util.Inl (eff_name, arg_typ) -> begin
out_c
end
| FStar_Util.Inr (c1) -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c1 ((x), (out_c)))
end)
end)) cres2 arg_comps_rev)
in (

let comp1 = (FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env None chead1 ((None), (comp)))
in (

let shortcuts_evaluation_order = (

let uu____5726 = (

let uu____5727 = (FStar_Syntax_Subst.compress head2)
in uu____5727.FStar_Syntax_Syntax.n)
in (match (uu____5726) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Or))
end
| uu____5731 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____5745 -> (match (uu____5745) with
| (arg, uu____5757, uu____5758) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = ((FStar_Syntax_Syntax.mk_Tm_app head2 args1) (Some (comp1.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres2.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ))))
end
| uu____5777 -> begin
(

let uu____5778 = (

let map_fun = (fun uu____5817 -> (match (uu____5817) with
| ((e, q), uu____5841, c0) -> begin
(match (c0) with
| FStar_Util.Inl (uu____5866) -> begin
((None), (((e), (q))))
end
| FStar_Util.Inr (c) when (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) -> begin
((None), (((e), (q))))
end
| FStar_Util.Inr (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____5909 = (

let uu____5912 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____5912), (q)))
in ((Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____5909)))))
end)
end))
in (

let uu____5930 = (

let uu____5944 = (

let uu____5957 = (

let uu____5969 = (

let uu____5978 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____5978), (None), (FStar_Util.Inr (chead1))))
in (uu____5969)::arg_comps_rev)
in (FStar_List.map map_fun uu____5957))
in (FStar_All.pipe_left FStar_List.split uu____5944))
in (match (uu____5930) with
| (lifted_args, reverse_args) -> begin
(

let uu____6087 = (

let uu____6088 = (FStar_List.hd reverse_args)
in (Prims.fst uu____6088))
in (

let uu____6093 = (

let uu____6097 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____6097))
in ((lifted_args), (uu____6087), (uu____6093))))
end)))
in (match (uu____5778) with
| (lifted_args, head3, args1) -> begin
(

let app = ((FStar_Syntax_Syntax.mk_Tm_app head3 args1) (Some (comp1.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres2.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___85_6165 -> (match (uu___85_6165) with
| None -> begin
e
end
| Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1)
in (

let letbinding = (

let uu____6207 = (

let uu____6210 = (

let uu____6211 = (

let uu____6219 = (

let uu____6220 = (

let uu____6221 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6221)::[])
in (FStar_Syntax_Subst.close uu____6220 e))
in ((((false), ((lb)::[]))), (uu____6219)))
in FStar_Syntax_Syntax.Tm_let (uu____6211))
in (FStar_Syntax_Syntax.mk uu____6210))
in (uu____6207 None e.FStar_Syntax_Syntax.pos))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp1.FStar_Syntax_Syntax.res_typ)))))))) None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____6255 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp1 guard1)
in (match (uu____6255) with
| (comp2, g) -> begin
((app), (comp2), (g))
end))))));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____6313 bs args1 -> (match (uu____6313) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (uu____6408))))::rest, ((uu____6410, None))::uu____6411) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let t1 = (check_no_escape (Some (head1)) env fvs t)
in (

let uu____6448 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____6448) with
| (varg, uu____6459, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____6472 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____6472)))
in (

let uu____6473 = (

let uu____6495 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst2), ((((arg), (None), (FStar_Util.Inl (((FStar_Syntax_Const.effect_Tot_lid), (t1))))))::outargs), ((arg)::arg_rets), (uu____6495), (fvs)))
in (tc_args head_info uu____6473 rest args1))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| uu____6586 -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___111_6593 = x
in {FStar_Syntax_Syntax.ppname = uu___111_6593.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___111_6593.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____6595 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____6595) with
| true -> begin
(

let uu____6596 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____6596))
end
| uu____6597 -> begin
()
end));
(

let targ1 = (check_no_escape (Some (head1)) env fvs targ)
in (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___112_6601 = env1
in {FStar_TypeChecker_Env.solver = uu___112_6601.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___112_6601.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___112_6601.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___112_6601.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___112_6601.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___112_6601.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___112_6601.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___112_6601.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___112_6601.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___112_6601.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___112_6601.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___112_6601.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___112_6601.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___112_6601.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___112_6601.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___112_6601.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___112_6601.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___112_6601.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___112_6601.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___112_6601.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___112_6601.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___112_6601.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___112_6601.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____6603 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____6603) with
| true -> begin
(

let uu____6604 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____6605 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6606 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____6604 uu____6605 uu____6606))))
end
| uu____6607 -> begin
()
end));
(

let uu____6608 = (tc_term env2 e)
in (match (uu____6608) with
| (e1, c, g_e) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e1), (aq))
in (

let uu____6624 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____6624) with
| true -> begin
(

let subst2 = (

let uu____6629 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____6629 e1))
in (tc_args head_info ((subst2), ((((arg), (None), (FStar_Util.Inl (((c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ))))))::outargs), ((arg)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____6684 -> begin
(

let uu____6685 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name)
in (match (uu____6685) with
| true -> begin
(

let subst2 = (

let uu____6690 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____6690 e1))
in (tc_args head_info ((subst2), ((((arg), (Some (x1)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____6735 -> begin
(

let uu____6736 = (

let uu____6737 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder uu____6737))
in (match (uu____6736) with
| true -> begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e1.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (

let uu____6746 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6746))
in (tc_args head_info ((subst1), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g1), (fvs)) rest rest')))
end
| uu____6783 -> begin
(

let uu____6784 = (

let uu____6806 = (

let uu____6808 = (

let uu____6809 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____6809))
in (uu____6808)::arg_rets)
in ((subst1), ((((arg), (Some (x1)), (FStar_Util.Inr (c))))::outargs), (uu____6806), (g1), ((x1)::fvs)))
in (tc_args head_info uu____6784 rest rest'))
end))
end))
end))))
end));
))));
)));
)
end
| (uu____6846, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____6867) -> begin
(

let uu____6897 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____6897) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 tres -> (

let tres1 = (

let uu____6920 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____6920 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____6936 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____6936) with
| (bs2, cres'1) -> begin
(

let head_info1 = ((head2), (chead1), (ghead1), ((FStar_Syntax_Util.lcomp_of_comp cres'1)))
in ((

let uu____6950 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6950) with
| true -> begin
(

let uu____6951 = (FStar_Range.string_of_range tres1.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" uu____6951))
end
| uu____6952 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____6981 when (not (norm1)) -> begin
(

let uu____6982 = (unfold_whnf env tres1)
in (aux true uu____6982))
end
| uu____6983 -> begin
(

let uu____6984 = (

let uu____6985 = (

let uu____6988 = (

let uu____6989 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____6990 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" uu____6989 uu____6990)))
in (

let uu____6994 = (FStar_Syntax_Syntax.argpos arg)
in ((uu____6988), (uu____6994))))
in FStar_Errors.Error (uu____6985))
in (Prims.raise uu____6984))
end)))
in (aux false chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf -> (

let uu____7007 = (

let uu____7008 = (unfold_whnf env tf)
in uu____7008.FStar_Syntax_Syntax.n)
in (match (uu____7007) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____7084 = (tc_term env1 e)
in (match (uu____7084) with
| (e1, c, g_e) -> begin
(

let uu____7097 = (tc_args1 env1 tl1)
in (match (uu____7097) with
| (args2, comps, g_rest) -> begin
(

let uu____7119 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____7119)))
end))
end))
end))
in (

let uu____7130 = (tc_args1 env args)
in (match (uu____7130) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____7152 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____7172 -> (match (uu____7172) with
| (uu____7180, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____7152))
in (

let ml_or_tot = (fun t r1 -> (

let uu____7196 = (FStar_Options.ml_ish ())
in (match (uu____7196) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____7197 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____7199 = (

let uu____7202 = (

let uu____7203 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7203 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____7202))
in (ml_or_tot uu____7199 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____7212 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____7212) with
| true -> begin
(

let uu____7213 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____7214 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____7215 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____7213 uu____7214 uu____7215))))
end
| uu____7216 -> begin
()
end));
(

let uu____7218 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____7218));
(

let comp = (

let uu____7220 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____7225 out -> (match (uu____7225) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____7220))
in (

let uu____7234 = ((FStar_Syntax_Syntax.mk_Tm_app head1 args1) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let uu____7241 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____7234), (comp), (uu____7241)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7256 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7256) with
| (bs1, c1) -> begin
(

let head_info = ((head1), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c1)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs1 args))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____7300) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____7306, uu____7307) -> begin
(check_function_app t)
end
| uu____7336 -> begin
(

let uu____7337 = (

let uu____7338 = (

let uu____7341 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((uu____7341), (head1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____7338))
in (Prims.raise uu____7337))
end)))
in (check_function_app thead))));
)))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head1 chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let uu____7392 = (FStar_List.fold_left2 (fun uu____7405 uu____7406 uu____7407 -> (match (((uu____7405), (uu____7406), (uu____7407))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((aq <> aq')) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7450 -> begin
()
end);
(

let uu____7451 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____7451) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____7463 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____7463 g))
in (

let ghost1 = (ghost || ((

let uu____7465 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____7465))) && (

let uu____7466 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____7466)))))
in (

let uu____7467 = (

let uu____7473 = (

let uu____7479 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____7479)::[])
in (FStar_List.append seen uu____7473))
in (

let uu____7484 = (FStar_TypeChecker_Rel.conj_guard guard g1)
in ((uu____7467), (uu____7484), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____7392) with
| (args1, guard, ghost) -> begin
(

let e = ((FStar_Syntax_Syntax.mk_Tm_app head1 args1) (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____7513 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____7513 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____7514 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____7515 = (FStar_TypeChecker_Util.strengthen_precondition None env e c1 guard)
in (match (uu____7515) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____7527 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____7549 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____7549) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____7575 = branch1
in (match (uu____7575) with
| (cpat, uu____7595, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let uu____7637 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (uu____7637) with
| (pat_bvs1, exps, p) -> begin
((

let uu____7659 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7659) with
| true -> begin
(

let uu____7660 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____7661 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____7660 uu____7661)))
end
| uu____7662 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs1)
in (

let uu____7664 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____7664) with
| (env1, uu____7677) -> begin
(

let env11 = (

let uu___113_7681 = env1
in {FStar_TypeChecker_Env.solver = uu___113_7681.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___113_7681.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___113_7681.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___113_7681.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___113_7681.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___113_7681.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___113_7681.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___113_7681.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___113_7681.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___113_7681.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___113_7681.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___113_7681.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___113_7681.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___113_7681.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___113_7681.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___113_7681.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___113_7681.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___113_7681.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___113_7681.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___113_7681.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___113_7681.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___113_7681.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___113_7681.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let uu____7683 = (

let uu____7688 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> ((

let uu____7700 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7700) with
| true -> begin
(

let uu____7701 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7702 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____7701 uu____7702)))
end
| uu____7703 -> begin
()
end));
(

let uu____7704 = (tc_term env11 e)
in (match (uu____7704) with
| (e1, lc, g) -> begin
((

let uu____7714 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7714) with
| true -> begin
(

let uu____7715 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____7716 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" uu____7715 uu____7716)))
end
| uu____7717 -> begin
()
end));
(

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g1 = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let uu____7720 = (

let uu____7721 = (FStar_TypeChecker_Rel.discharge_guard env (

let uu___114_7722 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___114_7722.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___114_7722.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___114_7722.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right uu____7721 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e1)
in (

let uvars_to_string = (fun uvs -> (

let uu____7736 = (

let uu____7738 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right uu____7738 (FStar_List.map (fun uu____7762 -> (match (uu____7762) with
| (u, uu____7767) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right uu____7736 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____7780 = (

let uu____7781 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____7781))
in (match (uu____7780) with
| true -> begin
(

let unresolved = (

let uu____7788 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right uu____7788 FStar_Util.set_elements))
in (

let uu____7802 = (

let uu____7803 = (

let uu____7806 = (

let uu____7807 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (

let uu____7808 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____7809 = (

let uu____7810 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____7822 -> (match (uu____7822) with
| (u, uu____7830) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____7810 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____7807 uu____7808 uu____7809))))
in ((uu____7806), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____7803))
in (Prims.raise uu____7802)))
end
| uu____7843 -> begin
()
end));
(

let uu____7845 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7845) with
| true -> begin
(

let uu____7846 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____7846))
end
| uu____7847 -> begin
()
end));
((e1), (e'));
))))))));
)
end));
))))
in (FStar_All.pipe_right uu____7688 FStar_List.unzip))
in (match (uu____7683) with
| (exps1, norm_exps) -> begin
(

let p1 = (FStar_TypeChecker_Util.decorate_pattern env p exps1)
in ((p1), (pat_bvs1), (pat_env), (exps1), (norm_exps)))
end))))
end)));
)
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let uu____7877 = (

let uu____7881 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____7881 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____7877) with
| (scrutinee_env, uu____7894) -> begin
(

let uu____7897 = (tc_pat true pat_t pattern)
in (match (uu____7897) with
| (pattern1, pat_bvs1, pat_env, disj_exps, norm_disj_exps) -> begin
(

let uu____7925 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
(

let uu____7940 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____7940) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7947 -> begin
(

let uu____7948 = (

let uu____7952 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term uu____7952 e))
in (match (uu____7948) with
| (e1, c, g) -> begin
((Some (e1)), (g))
end))
end))
end)
in (match (uu____7925) with
| (when_clause1, g_when) -> begin
(

let uu____7972 = (tc_term pat_env branch_exp)
in (match (uu____7972) with
| (branch_exp1, c, g_branch) -> begin
(

let when_condition = (match (when_clause1) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____7991 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____7991))
end)
in (

let uu____7993 = (

let eqs = (

let uu____7999 = (

let uu____8000 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8000)))
in (match (uu____7999) with
| true -> begin
None
end
| uu____8002 -> begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| uu____8014 -> begin
(

let clause = (

let uu____8016 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____8016 pat_t scrutinee_tm e1))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(

let uu____8019 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____8019))
end))
end))) None))
end))
in (

let uu____8029 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp1 c g_branch)
in (match (uu____8029) with
| (c1, g_branch1) -> begin
(

let uu____8039 = (match (((eqs), (when_condition))) with
| uu____8046 when (

let uu____8051 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8051))) -> begin
((c1), (g_when))
end
| (None, None) -> begin
((c1), (g_when))
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (

let uu____8059 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____8060 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____8059), (uu____8060))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____8067 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____8067))
in (

let uu____8068 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____8069 = (

let uu____8070 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____8070 g_when))
in ((uu____8068), (uu____8069))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____8076 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____8076), (g_when)))))
end)
in (match (uu____8039) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let uu____8084 = (FStar_TypeChecker_Util.close_comp env pat_bvs1 c_weak)
in (

let uu____8085 = (FStar_TypeChecker_Rel.close_guard env binders g_when_weak)
in ((uu____8084), (uu____8085), (g_branch1)))))
end))
end)))
in (match (uu____7993) with
| (c1, g_when1, g_branch1) -> begin
(

let branch_guard = (

let uu____8098 = (

let uu____8099 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8099)))
in (match (uu____8098) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____8100 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pat_exp -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____8130 = (

let uu____8131 = (

let uu____8132 = (

let uu____8134 = (

let uu____8138 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____8138))
in (Prims.snd uu____8134))
in (FStar_List.length uu____8132))
in (uu____8131 > (Prims.parse_int "1")))
in (match (uu____8130) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____8147 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____8147) with
| None -> begin
[]
end
| uu____8158 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational None)
in (

let disc1 = (

let uu____8168 = (

let uu____8169 = (

let uu____8170 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____8170)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____8169))
in (uu____8168 None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____8175 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Const.exp_true_bool)
in (uu____8175)::[])))
end)))
end
| uu____8176 -> begin
[]
end)))
in (

let fail = (fun uu____8183 -> (

let uu____8184 = (

let uu____8185 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (

let uu____8186 = (FStar_Syntax_Print.term_to_string pat_exp)
in (

let uu____8187 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____8185 uu____8186 uu____8187))))
in (failwith uu____8184)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____8208) -> begin
(head_constructor t1)
end
| uu____8214 -> begin
(fail ())
end))
in (

let pat_exp1 = (

let uu____8217 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right uu____8217 FStar_Syntax_Util.unmeta))
in (match (pat_exp1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (c2) -> begin
(

let uu____8234 = (

let uu____8235 = (tc_constant pat_exp1.FStar_Syntax_Syntax.pos c2)
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____8235 scrutinee_tm1 pat_exp1))
in (uu____8234)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp1)
in (

let uu____8243 = (

let uu____8244 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____8244)))
in (match (uu____8243) with
| true -> begin
[]
end
| uu____8250 -> begin
(

let uu____8251 = (head_constructor pat_exp1)
in (discriminate scrutinee_tm1 uu____8251))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let f = (head_constructor head1)
in (

let uu____8278 = (

let uu____8279 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____8279)))
in (match (uu____8278) with
| true -> begin
[]
end
| uu____8285 -> begin
(

let sub_term_guards = (

let uu____8288 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____8304 -> (match (uu____8304) with
| (ei, uu____8311) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____8321 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____8321) with
| None -> begin
[]
end
| uu____8332 -> begin
(

let sub_term = (

let uu____8341 = (

let uu____8342 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (

let uu____8347 = (

let uu____8348 = (FStar_Syntax_Syntax.as_arg scrutinee_tm1)
in (uu____8348)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____8342 uu____8347)))
in (uu____8341 None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____8288 FStar_List.flatten))
in (

let uu____8360 = (discriminate scrutinee_tm1 f)
in (FStar_List.append uu____8360 sub_term_guards)))
end)))
end
| uu____8364 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pat -> (

let uu____8376 = (

let uu____8377 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8377)))
in (match (uu____8376) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end
| uu____8378 -> begin
(

let t = (

let uu____8380 = (build_branch_guard scrutinee_tm1 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____8380))
in (

let uu____8383 = (FStar_Syntax_Util.type_u ())
in (match (uu____8383) with
| (k, uu____8387) -> begin
(

let uu____8388 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____8388) with
| (t1, uu____8393, uu____8394) -> begin
t1
end))
end)))
end)))
in (

let branch_guard = (

let uu____8396 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right uu____8396 FStar_Syntax_Util.mk_disj_l))
in (

let branch_guard1 = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard1))))
end))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g_when1 g_branch1)
in ((

let uu____8407 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8407) with
| true -> begin
(

let uu____8408 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____8408))
end
| uu____8409 -> begin
()
end));
(

let uu____8410 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in ((uu____8410), (branch_guard), (c1), (guard)));
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

let uu____8428 = (check_let_bound_def true env1 lb)
in (match (uu____8428) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____8442 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
((g1), (e1), (univ_vars1), (c1))
end
| uu____8451 -> begin
(

let g11 = (

let uu____8453 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____8453 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____8455 = (

let uu____8460 = (

let uu____8466 = (

let uu____8471 = (

let uu____8479 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____8479)))
in (uu____8471)::[])
in (FStar_TypeChecker_Util.generalize env1 uu____8466))
in (FStar_List.hd uu____8460))
in (match (uu____8455) with
| (uu____8508, univs1, e11, c11) -> begin
((g11), (e11), (univs1), ((FStar_Syntax_Util.lcomp_of_comp c11)))
end)))
end)
in (match (uu____8442) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____8519 = (

let uu____8524 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____8524) with
| true -> begin
(

let uu____8529 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____8529) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____8544 -> begin
((

let uu____8546 = (FStar_Options.warn_top_level_effects ())
in (match (uu____8546) with
| true -> begin
(

let uu____8547 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.warn uu____8547 FStar_TypeChecker_Err.top_level_effect))
end
| uu____8548 -> begin
()
end));
(

let uu____8549 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))))) None e2.FStar_Syntax_Syntax.pos)
in ((uu____8549), (c12)));
)
end)
end))
end
| uu____8564 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____8567 = (c11.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right uu____8567 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env1)))
in (

let e21 = (

let uu____8575 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____8575) with
| true -> begin
e2
end
| uu____8578 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))))) None e2.FStar_Syntax_Syntax.pos)
end))
in ((e21), (c))));
)
end))
in (match (uu____8519) with
| (e21, c12) -> begin
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_TypeChecker_Common.t_unit)
in ((FStar_ST.write e21.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e11)
in (

let uu____8607 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((uu____8607), ((FStar_Syntax_Util.lcomp_of_comp cres)), (FStar_TypeChecker_Rel.trivial_guard))));
))
end))
end))
end))
end
| uu____8626 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___115_8647 = env1
in {FStar_TypeChecker_Env.solver = uu___115_8647.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___115_8647.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___115_8647.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___115_8647.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___115_8647.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___115_8647.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___115_8647.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___115_8647.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___115_8647.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___115_8647.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___115_8647.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___115_8647.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___115_8647.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___115_8647.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___115_8647.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___115_8647.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___115_8647.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___115_8647.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___115_8647.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___115_8647.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___115_8647.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___115_8647.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___115_8647.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____8648 = (

let uu____8654 = (

let uu____8655 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____8655 Prims.fst))
in (check_let_bound_def false uu____8654 lb))
in (match (uu____8648) with
| (e1, uu____8667, c1, g1, annotated) -> begin
(

let x = (

let uu___116_8672 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___116_8672.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_8672.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____8673 = (

let uu____8676 = (

let uu____8677 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____8677)::[])
in (FStar_Syntax_Subst.open_term uu____8676 e2))
in (match (uu____8673) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (Prims.fst xbinder)
in (

let uu____8689 = (

let uu____8693 = (FStar_TypeChecker_Env.push_bv env2 x1)
in (tc_term uu____8693 e21))
in (match (uu____8689) with
| (e22, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env2 (Some (e1)) c1 ((Some (x1)), (c2)))
in (

let e11 = (FStar_TypeChecker_Util.maybe_lift env2 e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e23 = (FStar_TypeChecker_Util.maybe_lift env2 e22 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let lb1 = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x1)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e11)
in (

let e3 = (

let uu____8708 = (

let uu____8711 = (

let uu____8712 = (

let uu____8720 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____8720)))
in FStar_Syntax_Syntax.Tm_let (uu____8712))
in (FStar_Syntax_Syntax.mk uu____8711))
in (uu____8708 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____8735 = (

let uu____8736 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____8737 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____8736 c1.FStar_Syntax_Syntax.res_typ uu____8737 e11)))
in (FStar_All.pipe_left (fun _0_32 -> FStar_TypeChecker_Common.NonTrivial (_0_32)) uu____8735))
in (

let g21 = (

let uu____8739 = (

let uu____8740 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____8740 g2))
in (FStar_TypeChecker_Rel.close_guard env2 xb uu____8739))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g21)
in (

let uu____8742 = (

let uu____8743 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____8743))
in (match (uu____8742) with
| true -> begin
(

let tt = (

let uu____8749 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____8749 FStar_Option.get))
in ((

let uu____8753 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____8753) with
| true -> begin
(

let uu____8754 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____8755 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____8754 uu____8755)))
end
| uu____8756 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____8757 -> begin
(

let t = (check_no_escape None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____8760 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____8760) with
| true -> begin
(

let uu____8761 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____8762 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____8761 uu____8762)))
end
| uu____8763 -> begin
()
end));
((e4), ((

let uu___117_8764 = cres
in {FStar_Syntax_Syntax.eff_name = uu___117_8764.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___117_8764.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___117_8764.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____8765 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8786 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8786) with
| (lbs1, e21) -> begin
(

let uu____8797 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____8797) with
| (env0, topt) -> begin
(

let uu____8808 = (build_let_rec_env true env0 lbs1)
in (match (uu____8808) with
| (lbs2, rec_env) -> begin
(

let uu____8819 = (check_let_recs rec_env lbs2)
in (match (uu____8819) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____8831 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g_lbs)
in (FStar_All.pipe_right uu____8831 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (

let uu____8835 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____8835 (fun _0_33 -> Some (_0_33))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (match ((lb.FStar_Syntax_Syntax.lbunivs = [])) with
| true -> begin
lb
end
| uu____8851 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end))))
end
| uu____8852 -> begin
(

let ecs = (

let uu____8859 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____8881 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____8881))))))
in (FStar_TypeChecker_Util.generalize env1 uu____8859))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____8901 -> (match (uu____8901) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (

let uu____8926 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8926))
in ((FStar_ST.write e21.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let uu____8935 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____8935) with
| (lbs5, e22) -> begin
(

let uu____8946 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____8961 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in ((uu____8946), (cres), (uu____8961))))
end));
)))))
end))
end))
end))
end))
end
| uu____8964 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8985 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8985) with
| (lbs1, e21) -> begin
(

let uu____8996 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____8996) with
| (env0, topt) -> begin
(

let uu____9007 = (build_let_rec_env false env0 lbs1)
in (match (uu____9007) with
| (lbs2, rec_env) -> begin
(

let uu____9018 = (check_let_recs rec_env lbs2)
in (match (uu____9018) with
| (lbs3, g_lbs) -> begin
(

let uu____9029 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___118_9040 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___118_9040.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_9040.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___119_9042 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___119_9042.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___119_9042.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___119_9042.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___119_9042.FStar_Syntax_Syntax.lbdef})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____9029) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____9059 = (tc_term env2 e21)
in (match (uu____9059) with
| (e22, cres, g2) -> begin
(

let guard = (

let uu____9070 = (

let uu____9071 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Rel.close_guard env2 uu____9071 g2))
in (FStar_TypeChecker_Rel.conj_guard g_lbs uu____9070))
in (

let cres1 = (FStar_TypeChecker_Util.close_comp env2 bvs cres)
in (

let tres = (norm env2 cres1.FStar_Syntax_Syntax.res_typ)
in (

let cres2 = (

let uu___120_9075 = cres1
in {FStar_Syntax_Syntax.eff_name = uu___120_9075.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___120_9075.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___120_9075.FStar_Syntax_Syntax.comp})
in (

let uu____9076 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____9076) with
| (lbs5, e23) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23))))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (uu____9105) -> begin
((e), (cres2), (guard))
end
| None -> begin
(

let tres1 = (check_no_escape None env2 bvs tres)
in (

let cres3 = (

let uu___121_9110 = cres2
in {FStar_Syntax_Syntax.eff_name = uu___121_9110.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___121_9110.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___121_9110.FStar_Syntax_Syntax.comp})
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
| uu____9113 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let uu____9129 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____9129) with
| (uu____9135, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let uu____9146 = (FStar_List.fold_left (fun uu____9153 lb -> (match (uu____9153) with
| (lbs1, env1) -> begin
(

let uu____9165 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____9165) with
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
| uu____9178 -> begin
(

let uu____9179 = (

let uu____9183 = (

let uu____9184 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst uu____9184))
in (tc_check_tot_or_gtot_term (

let uu___122_9189 = env0
in {FStar_TypeChecker_Env.solver = uu___122_9189.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___122_9189.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___122_9189.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___122_9189.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___122_9189.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___122_9189.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___122_9189.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___122_9189.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___122_9189.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___122_9189.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___122_9189.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___122_9189.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___122_9189.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___122_9189.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___122_9189.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___122_9189.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___122_9189.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___122_9189.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___122_9189.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___122_9189.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___122_9189.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___122_9189.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___122_9189.FStar_TypeChecker_Env.qname_and_index}) t uu____9183))
in (match (uu____9179) with
| (t1, uu____9191, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((

let uu____9195 = (FStar_TypeChecker_Rel.discharge_guard env2 g1)
in (FStar_All.pipe_left Prims.ignore uu____9195));
(norm env0 t1);
))
end))
end)
in (

let env3 = (

let uu____9197 = ((termination_check_enabled t1) && (FStar_TypeChecker_Env.should_verify env2))
in (match (uu____9197) with
| true -> begin
(

let uu___123_9198 = env2
in {FStar_TypeChecker_Env.solver = uu___123_9198.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___123_9198.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___123_9198.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___123_9198.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___123_9198.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___123_9198.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___123_9198.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___123_9198.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___123_9198.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___123_9198.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___123_9198.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___123_9198.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___123_9198.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___123_9198.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___123_9198.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___123_9198.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___123_9198.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___123_9198.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___123_9198.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___123_9198.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___123_9198.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___123_9198.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___123_9198.FStar_TypeChecker_Env.qname_and_index})
end
| uu____9205 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname (([]), (t1)))
end))
in (

let lb1 = (

let uu___124_9208 = lb
in {FStar_Syntax_Syntax.lbname = uu___124_9208.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___124_9208.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb1)::lbs1), (env3)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____9146) with
| (lbs1, env1) -> begin
(((FStar_List.rev lbs1)), (env1))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____9222 = (

let uu____9227 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____9238 = (

let uu____9242 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____9242 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____9238) with
| (e, c, g) -> begin
((

let uu____9249 = (

let uu____9250 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____9250)))
in (match (uu____9249) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____9251 -> begin
()
end));
(

let lb1 = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb1), (g)));
)
end)))))
in (FStar_All.pipe_right uu____9227 FStar_List.unzip))
in (match (uu____9222) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____9279 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9279) with
| (env1, uu____9289) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____9295 = (check_lbtyp top_level env lb)
in (match (uu____9295) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (univ_vars1 <> []))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____9318 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____9321 = (tc_maybe_toplevel_term (

let uu___125_9325 = env11
in {FStar_TypeChecker_Env.solver = uu___125_9325.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___125_9325.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___125_9325.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___125_9325.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___125_9325.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___125_9325.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___125_9325.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___125_9325.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___125_9325.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___125_9325.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___125_9325.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___125_9325.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___125_9325.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___125_9325.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___125_9325.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___125_9325.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___125_9325.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___125_9325.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___125_9325.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___125_9325.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___125_9325.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___125_9325.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___125_9325.FStar_TypeChecker_Env.qname_and_index}) e11)
in (match (uu____9321) with
| (e12, c1, g1) -> begin
(

let uu____9334 = (

let uu____9337 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____9340 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____9337 e12 c1 wf_annot))
in (match (uu____9334) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____9350 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9350) with
| true -> begin
(

let uu____9351 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____9352 = (FStar_Syntax_Print.term_to_string c11.FStar_Syntax_Syntax.res_typ)
in (

let uu____9353 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" uu____9351 uu____9352 uu____9353))))
end
| uu____9354 -> begin
()
end));
((e12), (univ_vars1), (c11), (g11), ((FStar_Option.isSome topt)));
))
end))
end)));
)
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.subst_elt Prims.list * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end
| uu____9375 -> begin
()
end);
((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____9379 -> begin
(

let uu____9380 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____9380) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____9407 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((Some (t1)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____9407)))
end
| uu____9411 -> begin
(

let uu____9412 = (FStar_Syntax_Util.type_u ())
in (match (uu____9412) with
| (k, uu____9423) -> begin
(

let uu____9424 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____9424) with
| (t2, uu____9436, g) -> begin
((

let uu____9439 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____9439) with
| true -> begin
(

let uu____9440 = (

let uu____9441 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____9441))
in (

let uu____9442 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____9440 uu____9442)))
end
| uu____9443 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____9445 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((Some (t3)), (g), (univ_vars1), (univ_opening), (uu____9445))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____9450 -> (match (uu____9450) with
| (x, imp) -> begin
(

let uu____9461 = (FStar_Syntax_Util.type_u ())
in (match (uu____9461) with
| (tu, u) -> begin
((

let uu____9473 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9473) with
| true -> begin
(

let uu____9474 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____9475 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____9476 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____9474 uu____9475 uu____9476))))
end
| uu____9477 -> begin
()
end));
(

let uu____9478 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____9478) with
| (t, uu____9489, g) -> begin
(

let x1 = (((

let uu___126_9494 = x
in {FStar_Syntax_Syntax.ppname = uu___126_9494.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___126_9494.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____9496 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____9496) with
| true -> begin
(

let uu____9497 = (FStar_Syntax_Print.bv_to_string (Prims.fst x1))
in (

let uu____9498 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____9497 uu____9498)))
end
| uu____9499 -> begin
()
end));
(

let uu____9500 = (push_binding env x1)
in ((x1), (uu____9500), (g), (u)));
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

let uu____9551 = (tc_binder env1 b)
in (match (uu____9551) with
| (b1, env', g, u) -> begin
(

let uu____9574 = (aux env' bs2)
in (match (uu____9574) with
| (bs3, env'1, g', us) -> begin
(

let uu____9603 = (

let uu____9604 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____9604))
in (((b1)::bs3), (env'1), (uu____9603), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____9647 uu____9648 -> (match (((uu____9647), (uu____9648))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____9685 = (tc_term env1 t)
in (match (uu____9685) with
| (t1, uu____9695, g') -> begin
(

let uu____9697 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____9697)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____9715 -> (match (uu____9715) with
| (pats1, g) -> begin
(

let uu____9729 = (tc_args env p)
in (match (uu____9729) with
| (args, g') -> begin
(

let uu____9737 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats1), (uu____9737)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____9745 = (tc_maybe_toplevel_term env e)
in (match (uu____9745) with
| (e1, c, g) -> begin
(

let uu____9755 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____9755) with
| true -> begin
((e1), (c), (g))
end
| uu____9759 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (c.FStar_Syntax_Syntax.comp ())
in (

let c2 = (norm_c env c1)
in (

let uu____9765 = (

let uu____9768 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____9768) with
| true -> begin
(

let uu____9771 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____9771), (false)))
end
| uu____9772 -> begin
(

let uu____9773 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____9773), (true)))
end))
in (match (uu____9765) with
| (target_comp, allow_ghost) -> begin
(

let uu____9779 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____9779) with
| Some (g') -> begin
(

let uu____9785 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in ((e1), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (uu____9785)))
end
| uu____9786 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____9791 = (

let uu____9792 = (

let uu____9795 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in ((uu____9795), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____9792))
in (Prims.raise uu____9791))
end
| uu____9799 -> begin
(

let uu____9800 = (

let uu____9801 = (

let uu____9804 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in ((uu____9804), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____9801))
in (Prims.raise uu____9800))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____9817 = (tc_tot_or_gtot_term env t)
in (match (uu____9817) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____9837 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____9837) with
| true -> begin
(

let uu____9838 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____9838))
end
| uu____9839 -> begin
()
end));
(

let env1 = (

let uu___127_9841 = env
in {FStar_TypeChecker_Env.solver = uu___127_9841.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___127_9841.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___127_9841.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___127_9841.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___127_9841.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___127_9841.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___127_9841.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___127_9841.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___127_9841.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___127_9841.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___127_9841.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___127_9841.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___127_9841.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___127_9841.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___127_9841.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___127_9841.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___127_9841.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___127_9841.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___127_9841.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___127_9841.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___127_9841.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____9844 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)
with
| FStar_Errors.Error (msg, uu____9860) -> begin
(

let uu____9861 = (

let uu____9862 = (

let uu____9865 = (FStar_TypeChecker_Env.get_range env1)
in (((Prims.strcat "Implicit argument: " msg)), (uu____9865)))
in FStar_Errors.Error (uu____9862))
in (Prims.raise uu____9861))
end
in (match (uu____9844) with
| (t, c, g) -> begin
(

let uu____9875 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____9875) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____9881 -> begin
(

let uu____9882 = (

let uu____9883 = (

let uu____9886 = (

let uu____9887 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____9887))
in (

let uu____9888 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____9886), (uu____9888))))
in FStar_Errors.Error (uu____9883))
in (Prims.raise uu____9882))
end))
end)));
))


let level_of_type_fail = (fun env e t -> (

let uu____9909 = (

let uu____9910 = (

let uu____9913 = (

let uu____9914 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____9914 t))
in (

let uu____9915 = (FStar_TypeChecker_Env.get_range env)
in ((uu____9913), (uu____9915))))
in FStar_Errors.Error (uu____9910))
in (Prims.raise uu____9909)))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____9932 = (

let uu____9933 = (FStar_Syntax_Util.unrefine t1)
in uu____9933.FStar_Syntax_Syntax.n)
in (match (uu____9932) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____9937 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____9939 -> begin
(

let uu____9940 = (FStar_Syntax_Util.type_u ())
in (match (uu____9940) with
| (t_u, u) -> begin
(

let env1 = (

let uu___130_9946 = env
in {FStar_TypeChecker_Env.solver = uu___130_9946.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___130_9946.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___130_9946.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___130_9946.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___130_9946.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___130_9946.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___130_9946.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___130_9946.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___130_9946.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___130_9946.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___130_9946.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___130_9946.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___130_9946.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___130_9946.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___130_9946.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___130_9946.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___130_9946.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___130_9946.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___130_9946.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___130_9946.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___130_9946.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___130_9946.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___130_9946.FStar_TypeChecker_Env.qname_and_index})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____9950 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____9950))
end
| uu____9951 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____9960 = (

let uu____9961 = (FStar_Syntax_Subst.compress e)
in uu____9961.FStar_Syntax_Syntax.n)
in (match (uu____9960) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____9970) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____9981) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10006, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____10021) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____10028 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10028) with
| ((uu____10039, t), uu____10041) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____10044, (FStar_Util.Inl (t), uu____10046), uu____10047) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____10083, (FStar_Util.Inr (c), uu____10085), uu____10086) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u)))) None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____10133; FStar_Syntax_Syntax.pos = uu____10134; FStar_Syntax_Syntax.vars = uu____10135}, us) -> begin
(

let uu____10141 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10141) with
| ((us', t), uu____10154) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____10162 = (

let uu____10163 = (

let uu____10166 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____10166)))
in FStar_Errors.Error (uu____10163))
in (Prims.raise uu____10162))
end
| uu____10167 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____10174 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____10175) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____10183) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____10200 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____10200) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____10211 -> (match (uu____10211) with
| (b, uu____10215) -> begin
(

let uu____10216 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____10216))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____10221 = (universe_of_aux env res)
in (level_of_type env res uu____10221)))
in (

let u_c = (

let uu____10223 = (FStar_TypeChecker_Env.effect_repr env c1 u_res)
in (match (uu____10223) with
| None -> begin
u_res
end
| Some (trepr) -> begin
(

let uu____10226 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____10226))
end))
in (

let u = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max ((u_c)::us)))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None e.FStar_Syntax_Syntax.pos)))))
end))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rec type_of_head = (fun retry hd2 args1 -> (

let hd3 = (FStar_Syntax_Subst.compress hd2)
in (match (hd3.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_type (_)) -> begin
(

let uu____10312 = (universe_of_aux env hd3)
in ((uu____10312), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____10322, (hd4)::uu____10324) -> begin
(

let uu____10371 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____10371) with
| (uu____10381, uu____10382, hd5) -> begin
(

let uu____10398 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____10398) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____10433 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____10435 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____10435) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____10470 -> begin
(

let uu____10471 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____10471) with
| (env1, uu____10485) -> begin
(

let env2 = (

let uu___131_10489 = env1
in {FStar_TypeChecker_Env.solver = uu___131_10489.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___131_10489.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___131_10489.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___131_10489.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___131_10489.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___131_10489.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___131_10489.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___131_10489.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___131_10489.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___131_10489.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___131_10489.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___131_10489.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___131_10489.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___131_10489.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___131_10489.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___131_10489.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___131_10489.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___131_10489.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___131_10489.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___131_10489.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___131_10489.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____10491 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____10491) with
| true -> begin
(

let uu____10492 = (

let uu____10493 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____10493))
in (

let uu____10494 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____10492 uu____10494)))
end
| uu____10495 -> begin
()
end));
(

let uu____10496 = (tc_term env2 hd3)
in (match (uu____10496) with
| (uu____10509, {FStar_Syntax_Syntax.eff_name = uu____10510; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____10512; FStar_Syntax_Syntax.comp = uu____10513}, g) -> begin
((

let uu____10523 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____10523 Prims.ignore));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____10531 = (type_of_head true hd1 args)
in (match (uu____10531) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____10560 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____10560) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match (((FStar_List.length bs) = (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____10592 -> begin
(

let uu____10593 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____10593))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____10596, (hd1)::uu____10598) -> begin
(

let uu____10645 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____10645) with
| (uu____10648, uu____10649, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____10665, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____10699 = (universe_of_aux env e)
in (level_of_type env e uu____10699)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____10712 = (tc_binders env tps)
in (match (uu____10712) with
| (tps1, env1, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
((tps1), (env1), (us));
)
end)))




