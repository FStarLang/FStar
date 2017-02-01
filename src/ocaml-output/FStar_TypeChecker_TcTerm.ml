
open Prims

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___82_4 = env
in {FStar_TypeChecker_Env.solver = uu___82_4.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___82_4.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___82_4.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___82_4.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___82_4.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___82_4.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___82_4.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___82_4.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___82_4.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___82_4.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___82_4.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___82_4.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___82_4.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___82_4.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___82_4.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___82_4.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___82_4.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___82_4.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___82_4.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___82_4.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___82_4.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___82_4.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___82_4.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___83_8 = env
in {FStar_TypeChecker_Env.solver = uu___83_8.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___83_8.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___83_8.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___83_8.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___83_8.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___83_8.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___83_8.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___83_8.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___83_8.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___83_8.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___83_8.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___83_8.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___83_8.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___83_8.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___83_8.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___83_8.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___83_8.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___83_8.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___83_8.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___83_8.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___83_8.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___83_8.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___83_8.FStar_TypeChecker_Env.qname_and_index}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = (match ((tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
| true -> begin
v.FStar_Syntax_Syntax.pos
end
| uu____33 -> begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end)
in (

let uu____34 = (

let uu____35 = (

let uu____36 = (FStar_Syntax_Syntax.as_arg v)
in (

let uu____37 = (

let uu____39 = (FStar_Syntax_Syntax.as_arg tl)
in (uu____39)::[])
in (uu____36)::uu____37))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____35))
in (uu____34 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun uu___76_47 -> (match (uu___76_47) with
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

let t = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____103 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t)
in (

let uu____106 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____106) with
| None -> begin
t
end
| Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t)
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
| Some (head) -> begin
(

let uu____118 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____119 = (FStar_TypeChecker_Normalize.term_to_string env head)
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

let uu____132 = (FStar_TypeChecker_Rel.try_teq env t s)
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


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> (

let uu____167 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____167) with
| true -> begin
s
end
| uu____168 -> begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let uu___84_181 = lc
in {FStar_Syntax_Syntax.eff_name = uu___84_181.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___84_181.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____182 -> (

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

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (

let uu____240 = (

let uu____241 = (FStar_Syntax_Subst.compress t)
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
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____291 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (uu____291) with
| (e, g) -> begin
((

let uu____300 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____300) with
| true -> begin
(

let uu____301 = (FStar_Syntax_Print.term_to_string t)
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
(FStar_All.pipe_left (fun _0_28 -> Some (_0_28)) (FStar_TypeChecker_Err.subtyping_failed env t t'))
end))
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____325 = (FStar_TypeChecker_Util.strengthen_precondition msg env e lc g)
in (match (uu____325) with
| (lc, g) -> begin
(

let uu____333 = (memo_tk e t')
in ((uu____333), ((set_lcomp_result lc t')), (g)))
end))));
)
end)))
end));
)
end))
in (match (uu____264) with
| (e, lc, g) -> begin
((

let uu____341 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____341) with
| true -> begin
(

let uu____342 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" uu____342))
end
| uu____343 -> begin
()
end));
((e), (lc), (g));
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
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
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

let c = (norm_c env c)
in ((

let uu____432 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____432) with
| true -> begin
(

let uu____433 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____434 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____435 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" uu____433 uu____434 uu____435))))
end
| uu____436 -> begin
()
end));
(

let uu____437 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (uu____437) with
| (e, uu____445, g) -> begin
(

let g = (

let uu____448 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____448 "could not prove post-condition" g))
in ((

let uu____450 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____450) with
| true -> begin
(

let uu____451 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____452 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" uu____451 uu____452)))
end
| uu____453 -> begin
()
end));
(

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c) (FStar_Syntax_Util.comp_result c))
in ((e), (expected_c), (g)));
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
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____486 = (

let uu____487 = (

let uu____490 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f)
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

let env = (

let uu___85_645 = env
in {FStar_TypeChecker_Env.solver = uu___85_645.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___85_645.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___85_645.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___85_645.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___85_645.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___85_645.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___85_645.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___85_645.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___85_645.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___85_645.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___85_645.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___85_645.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___85_645.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___85_645.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___85_645.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___85_645.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___85_645.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___85_645.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___85_645.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___85_645.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___85_645.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___85_645.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___85_645.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu____668 -> (match (uu____668) with
| (b, uu____673) -> begin
(

let t = (

let uu____675 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env uu____675))
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
| (head, uu____696) -> begin
(match (head.FStar_Syntax_Syntax.n) with
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

let uu____715 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___77_719 -> (match (uu___77_719) with
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

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun uu____788 -> (match (uu____788) with
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

let uu____803 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____803) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (

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

let uu____826 = (FStar_Util.prefix formals)
in (match (uu____826) with
| (bs, (last, imp)) -> begin
(

let last = (

let uu___86_852 = last
in (

let uu____853 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = uu___86_852.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___86_852.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____853}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in ((

let uu____870 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
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

let uu___87_1141 = env
in {FStar_TypeChecker_Env.solver = uu___87_1141.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___87_1141.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___87_1141.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___87_1141.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___87_1141.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___87_1141.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___87_1141.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___87_1141.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___87_1141.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___87_1141.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___87_1141.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___87_1141.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___87_1141.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___87_1141.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___87_1141.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___87_1141.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___87_1141.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___87_1141.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___87_1141.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___87_1141.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___87_1141.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___87_1141.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___87_1141.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (match ((e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____1148 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____1150 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____1150) with
| true -> begin
(

let uu____1151 = (

let uu____1152 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1152))
in (

let uu____1153 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" uu____1151 uu____1153)))
end
| uu____1154 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1159) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____1198 = (tc_tot_or_gtot_term env e)
in (match (uu____1198) with
| (e, c, g) -> begin
(

let g = (

let uu___88_1209 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___88_1209.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___88_1209.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___88_1209.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____1222 = (FStar_Syntax_Util.type_u ())
in (match (uu____1222) with
| (t, u) -> begin
(

let uu____1230 = (tc_check_tot_or_gtot_term env e t)
in (match (uu____1230) with
| (e, c, g) -> begin
(

let uu____1240 = (

let uu____1249 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1249) with
| (env, uu____1262) -> begin
(tc_pats env pats)
end))
in (match (uu____1240) with
| (pats, g') -> begin
(

let g' = (

let uu___89_1283 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___89_1283.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___89_1283.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___89_1283.FStar_TypeChecker_Env.implicits})
in (

let uu____1284 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats)))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____1295 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((uu____1284), (c), (uu____1295)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____1303 = (

let uu____1304 = (FStar_Syntax_Subst.compress e)
in uu____1304.FStar_Syntax_Syntax.n)
in (match (uu____1303) with
| FStar_Syntax_Syntax.Tm_let ((uu____1310, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____1312; FStar_Syntax_Syntax.lbtyp = uu____1313; FStar_Syntax_Syntax.lbeff = uu____1314; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____1332 = (

let uu____1336 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term uu____1336 e1))
in (match (uu____1332) with
| (e1, c1, g1) -> begin
(

let uu____1343 = (tc_term env e2)
in (match (uu____1343) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (

let uu____1358 = (

let uu____1361 = (

let uu____1362 = (

let uu____1370 = (

let uu____1374 = (

let uu____1376 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (uu____1376)::[])
in ((false), (uu____1374)))
in ((uu____1370), (e2)))
in FStar_Syntax_Syntax.Tm_let (uu____1362))
in (FStar_Syntax_Syntax.mk uu____1361))
in (uu____1358 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____1406 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (uu____1406)))))))
end))
end))
end
| uu____1409 -> begin
(

let uu____1410 = (tc_term env e)
in (match (uu____1410) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____1434)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let uu____1449 = (tc_term env e)
in (match (uu____1449) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), uu____1474) -> begin
(

let uu____1493 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1493) with
| (env0, uu____1501) -> begin
(

let uu____1504 = (tc_comp env0 expected_c)
in (match (uu____1504) with
| (expected_c, uu____1512, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let uu____1517 = (

let uu____1521 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____1521 e))
in (match (uu____1517) with
| (e, c', g') -> begin
(

let uu____1528 = (

let uu____1532 = (

let uu____1535 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (uu____1535)))
in (check_expected_effect env0 (Some (expected_c)) uu____1532))
in (match (uu____1528) with
| (e, expected_c, g'') -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c))))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (

let uu____1570 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____1570))
in (

let uu____1571 = (comp_check_expected_typ env e lc)
in (match (uu____1571) with
| (e, c, f2) -> begin
(

let uu____1581 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (uu____1581)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), uu____1584) -> begin
(

let uu____1603 = (FStar_Syntax_Util.type_u ())
in (match (uu____1603) with
| (k, u) -> begin
(

let uu____1611 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____1611) with
| (t, uu____1619, f) -> begin
(

let uu____1621 = (

let uu____1625 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term uu____1625 e))
in (match (uu____1621) with
| (e, c, g) -> begin
(

let uu____1632 = (

let uu____1635 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____1638 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____1635 e c f))
in (match (uu____1632) with
| (c, f) -> begin
(

let uu____1644 = (

let uu____1648 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name)))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env uu____1648 c))
in (match (uu____1644) with
| (e, c, f2) -> begin
(

let uu____1670 = (

let uu____1671 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f uu____1671))
in ((e), (c), (uu____1670)))
end))
end))
end))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd)::rest)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_)); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd)::rest)) -> begin
(

let rest = (hd)::rest
in (

let uu____1748 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1748) with
| (unary_op, uu____1762) -> begin
(

let head = (

let uu____1780 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[]))))) None uu____1780))
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest))))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____1824; FStar_Syntax_Syntax.pos = uu____1825; FStar_Syntax_Syntax.vars = uu____1826}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____1851 -> begin
()
end);
(

let uu____1852 = (

let uu____1856 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1856) with
| (env0, uu____1864) -> begin
(tc_term env0 e)
end))
in (match (uu____1852) with
| (e, c, g) -> begin
(

let uu____1873 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1873) with
| (reify_op, uu____1887) -> begin
(

let u_c = (

let uu____1903 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (uu____1903) with
| (uu____1907, c', uu____1909) -> begin
(

let uu____1910 = (

let uu____1911 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____1911.FStar_Syntax_Syntax.n)
in (match (uu____1910) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____1915 -> begin
(

let uu____1916 = (FStar_Syntax_Util.type_u ())
in (match (uu____1916) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq env c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g')
end
| None -> begin
(

let uu____1925 = (

let uu____1926 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____1927 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____1928 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____1926 uu____1927 uu____1928))))
in (failwith uu____1925))
end);
u;
))
end))
end))
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[]))))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (

let uu____1951 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____1951 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____1952 = (comp_check_expected_typ env e c)
in (match (uu____1952) with
| (e, c, g') -> begin
(

let uu____1962 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (uu____1962)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = uu____1964; FStar_Syntax_Syntax.pos = uu____1965; FStar_Syntax_Syntax.vars = uu____1966}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____1991 -> begin
()
end);
(

let no_reflect = (fun uu____1998 -> (

let uu____1999 = (

let uu____2000 = (

let uu____2003 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((uu____2003), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____2000))
in (Prims.raise uu____1999)))
in (

let uu____2007 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2007) with
| (reflect_op, uu____2021) -> begin
(

let uu____2036 = (FStar_TypeChecker_Env.effect_decl_opt env l)
in (match (uu____2036) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
(

let uu____2042 = (

let uu____2043 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____2043)))
in (match (uu____2042) with
| true -> begin
(no_reflect ())
end
| uu____2048 -> begin
(

let uu____2049 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2049) with
| (env_no_ex, topt) -> begin
(

let uu____2060 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____2075 = (

let uu____2078 = (

let uu____2079 = (

let uu____2089 = (

let uu____2091 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____2092 = (

let uu____2094 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____2094)::[])
in (uu____2091)::uu____2092))
in ((repr), (uu____2089)))
in FStar_Syntax_Syntax.Tm_app (uu____2079))
in (FStar_Syntax_Syntax.mk uu____2078))
in (uu____2075 None top.FStar_Syntax_Syntax.pos))
in (

let uu____2104 = (

let uu____2108 = (

let uu____2109 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____2109 Prims.fst))
in (tc_tot_or_gtot_term uu____2108 t))
in (match (uu____2104) with
| (t, uu____2126, g) -> begin
(

let uu____2128 = (

let uu____2129 = (FStar_Syntax_Subst.compress t)
in uu____2129.FStar_Syntax_Syntax.n)
in (match (uu____2128) with
| FStar_Syntax_Syntax.Tm_app (uu____2140, ((res, uu____2142))::((wp, uu____2144))::[]) -> begin
((t), (res), (wp), (g))
end
| uu____2178 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____2060) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____2202 = (

let uu____2205 = (tc_tot_or_gtot_term env_no_ex e)
in (match (uu____2205) with
| (e, c, g) -> begin
((

let uu____2215 = (

let uu____2216 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____2216))
in (match (uu____2215) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____2221 -> begin
()
end));
(

let uu____2222 = (FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____2222) with
| None -> begin
((

let uu____2227 = (

let uu____2231 = (

let uu____2234 = (

let uu____2235 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2236 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____2235 uu____2236)))
in ((uu____2234), (e.FStar_Syntax_Syntax.pos)))
in (uu____2231)::[])
in (FStar_TypeChecker_Err.add_errors env uu____2227));
(

let uu____2241 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (uu____2241)));
)
end
| Some (g') -> begin
(

let uu____2243 = (

let uu____2244 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____2244))
in ((e), (uu____2243)))
end));
)
end))
in (match (uu____2202) with
| (e, g) -> begin
(

let c = (

let uu____2251 = (

let uu____2252 = (

let uu____2253 = (

let uu____2254 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (uu____2254)::[])
in (

let uu____2255 = (

let uu____2261 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2261)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____2253; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____2255; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____2252))
in (FStar_All.pipe_right uu____2251 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[]))))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____2282 = (comp_check_expected_typ env e c)
in (match (uu____2282) with
| (e, c, g') -> begin
(

let uu____2292 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (uu____2292)))
end))))
end))
end))
end))
end))
end))
end)));
)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let env0 = env
in (

let env = (

let uu____2311 = (

let uu____2312 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____2312 Prims.fst))
in (FStar_All.pipe_right uu____2311 instantiate_both))
in ((

let uu____2321 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____2321) with
| true -> begin
(

let uu____2322 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____2323 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____2322 uu____2323)))
end
| uu____2324 -> begin
()
end));
(

let uu____2325 = (tc_term (no_inst env) head)
in (match (uu____2325) with
| (head, chead, g_head) -> begin
(

let uu____2335 = (

let uu____2339 = ((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head))
in (match (uu____2339) with
| true -> begin
(

let uu____2343 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args uu____2343))
end
| uu____2345 -> begin
(

let uu____2346 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args uu____2346))
end))
in (match (uu____2335) with
| (e, c, g) -> begin
((

let uu____2355 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2355) with
| true -> begin
(

let uu____2356 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____2356))
end
| uu____2357 -> begin
()
end));
(

let c = (

let uu____2359 = (((FStar_TypeChecker_Env.should_verify env) && (

let uu____2360 = (FStar_Syntax_Util.is_lcomp_partial_return c)
in (not (uu____2360)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____2359) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end
| uu____2361 -> begin
c
end))
in (

let uu____2362 = (comp_check_expected_typ env0 e c)
in (match (uu____2362) with
| (e, c, g') -> begin
(

let gimp = (

let uu____2373 = (

let uu____2374 = (FStar_Syntax_Subst.compress head)
in uu____2374.FStar_Syntax_Syntax.n)
in (match (uu____2373) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____2378) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let uu___90_2410 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___90_2410.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___90_2410.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___90_2410.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____2435 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (

let uu____2437 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g uu____2437))
in ((

let uu____2439 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2439) with
| true -> begin
(

let uu____2440 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____2441 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____2440 uu____2441)))
end
| uu____2442 -> begin
()
end));
((e), (c), (gres));
)))
end)));
)
end))
end));
)))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let uu____2471 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2471) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let uu____2483 = (tc_term env1 e1)
in (match (uu____2483) with
| (e1, c1, g1) -> begin
(

let uu____2493 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let uu____2499 = (FStar_Syntax_Util.type_u ())
in (match (uu____2499) with
| (k, uu____2505) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (

let uu____2507 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((uu____2507), (res_t))))
end))
end)
in (match (uu____2493) with
| (env_branches, res_t) -> begin
((

let uu____2514 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2514) with
| true -> begin
(

let uu____2515 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____2515))
end
| uu____2516 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____2566 = (

let uu____2569 = (FStar_List.fold_right (fun uu____2588 uu____2589 -> (match (((uu____2588), (uu____2589))) with
| ((uu____2621, f, c, g), (caccum, gaccum)) -> begin
(

let uu____2654 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (uu____2654)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____2569) with
| (cases, g) -> begin
(

let uu____2675 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((uu____2675), (g)))
end))
in (match (uu____2566) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____2728 -> (match (uu____2728) with
| ((pat, wopt, br), uu____2744, lc, uu____2746) -> begin
(

let uu____2753 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (uu____2753)))
end))))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name)))))) None e.FStar_Syntax_Syntax.pos)))))
in (

let uu____2793 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____2793) with
| true -> begin
(mk_match e1)
end
| uu____2796 -> begin
(

let e_match = (

let uu____2800 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____2800))
in (

let lb = (

let uu____2804 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = uu____2804; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = (

let uu____2808 = (

let uu____2811 = (

let uu____2812 = (

let uu____2820 = (

let uu____2821 = (

let uu____2822 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____2822)::[])
in (FStar_Syntax_Subst.close uu____2821 e_match))
in ((((false), ((lb)::[]))), (uu____2820)))
in FStar_Syntax_Syntax.Tm_let (uu____2812))
in (FStar_Syntax_Syntax.mk uu____2811))
in (uu____2808 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____2836 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2836) with
| true -> begin
(

let uu____2837 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____2838 = (

let uu____2839 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2839))
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____2837 uu____2838)))
end
| uu____2840 -> begin
()
end));
(

let uu____2841 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (uu____2841)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2844); FStar_Syntax_Syntax.lbunivs = uu____2845; FStar_Syntax_Syntax.lbtyp = uu____2846; FStar_Syntax_Syntax.lbeff = uu____2847; FStar_Syntax_Syntax.lbdef = uu____2848})::[]), uu____2849) -> begin
((

let uu____2864 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2864) with
| true -> begin
(

let uu____2865 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____2865))
end
| uu____2866 -> begin
()
end));
(check_top_level_let env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____2867), uu____2868) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2878); FStar_Syntax_Syntax.lbunivs = uu____2879; FStar_Syntax_Syntax.lbtyp = uu____2880; FStar_Syntax_Syntax.lbeff = uu____2881; FStar_Syntax_Syntax.lbdef = uu____2882})::uu____2883), uu____2884) -> begin
((

let uu____2900 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2900) with
| true -> begin
(

let uu____2901 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____2901))
end
| uu____2902 -> begin
()
end));
(check_top_level_let_rec env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____2903), uu____2904) -> begin
(check_inner_let_rec env top)
end));
)))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let uu____2948 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____2948) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____2961 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2961) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____2964 -> begin
(

let uu____2965 = (

let uu____2966 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____2966))
in FStar_Util.Inr (uu____2965))
end))
in (

let is_data_ctor = (fun uu___78_2975 -> (match (uu___78_2975) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| uu____2978 -> begin
false
end))
in (

let uu____2980 = ((is_data_ctor dc) && (

let uu____2981 = (FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)
in (not (uu____2981))))
in (match (uu____2980) with
| true -> begin
(

let uu____2987 = (

let uu____2988 = (

let uu____2991 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____2994 = (FStar_TypeChecker_Env.get_range env)
in ((uu____2991), (uu____2994))))
in FStar_Errors.Error (uu____2988))
in (Prims.raise uu____2987))
end
| uu____2998 -> begin
(value_check_expected_typ env e tc implicits)
end))))
end)))
in (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____3005 = (

let uu____3006 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____3006))
in (failwith uu____3005))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____3025 = (

let uu____3026 = (FStar_Syntax_Subst.compress t1)
in uu____3026.FStar_Syntax_Syntax.n)
in (match (uu____3025) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3029) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____3037 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___91_3057 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___91_3057.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___91_3057.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___91_3057.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3085 = (

let uu____3092 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____3092) with
| None -> begin
(

let uu____3100 = (FStar_Syntax_Util.type_u ())
in (match (uu____3100) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____3085) with
| (t, uu____3121, g0) -> begin
(

let uu____3129 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (uu____3129) with
| (e, uu____3140, g1) -> begin
(

let uu____3148 = (

let uu____3149 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____3149 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____3150 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (uu____3148), (uu____3150))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (match (env.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____3157 -> begin
(FStar_TypeChecker_Env.lookup_bv env x)
end)
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let uu___92_3159 = x
in {FStar_Syntax_Syntax.ppname = uu___92_3159.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___92_3159.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let uu____3160 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____3160) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____3173 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____3173) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____3176 -> begin
(

let uu____3177 = (

let uu____3178 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3178))
in FStar_Util.Inr (uu____3177))
end))
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____3184; FStar_Syntax_Syntax.pos = uu____3185; FStar_Syntax_Syntax.vars = uu____3186}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let uu____3194 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3194) with
| (us', t) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____3211 = (

let uu____3212 = (

let uu____3215 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____3215)))
in FStar_Errors.Error (uu____3212))
in (Prims.raise uu____3211))
end
| uu____3216 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____3223 -> begin
(failwith "Impossible")
end)) us' us)
end);
(

let fv' = (

let uu___93_3225 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___94_3226 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___94_3226.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___94_3226.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___93_3225.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___93_3225.FStar_Syntax_Syntax.fv_qual})
in (

let e = (

let uu____3240 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3240 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3252 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3252) with
| (us, t) -> begin
((

let uu____3265 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Range")))
in (match (uu____3265) with
| true -> begin
(

let uu____3266 = (

let uu____3267 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____3267))
in (

let uu____3268 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____3269 = (

let uu____3270 = (

let uu____3271 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid uu____3271))
in (FStar_Range.string_of_range uu____3270))
in (

let uu____3272 = (

let uu____3273 = (

let uu____3274 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid uu____3274))
in (FStar_Range.string_of_use_range uu____3273))
in (

let uu____3275 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s" uu____3266 uu____3268 uu____3269 uu____3272 uu____3275))))))
end
| uu____3276 -> begin
()
end));
(

let fv' = (

let uu___95_3278 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___96_3279 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___96_3279.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___96_3279.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___95_3278.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___95_3278.FStar_Syntax_Syntax.fv_qual})
in (

let e = (

let uu____3293 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3293 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)));
)
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3329 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3329) with
| (bs, c) -> begin
(

let env0 = env
in (

let uu____3338 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3338) with
| (env, uu____3346) -> begin
(

let uu____3349 = (tc_binders env bs)
in (match (uu____3349) with
| (bs, env, g, us) -> begin
(

let uu____3361 = (tc_comp env c)
in (match (uu____3361) with
| (c, uc, f) -> begin
(

let e = (

let uu___97_3374 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = uu___97_3374.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___97_3374.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___97_3374.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env e bs c);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____3395 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g uu____3395))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))));
))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (tc_universe env u)
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u)))) None top.FStar_Syntax_Syntax.pos)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____3430 = (

let uu____3433 = (

let uu____3434 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3434)::[])
in (FStar_Syntax_Subst.open_term uu____3433 phi))
in (match (uu____3430) with
| (x, phi) -> begin
(

let env0 = env
in (

let uu____3441 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3441) with
| (env, uu____3449) -> begin
(

let uu____3452 = (

let uu____3459 = (FStar_List.hd x)
in (tc_binder env uu____3459))
in (match (uu____3452) with
| (x, env, f1, u) -> begin
((

let uu____3476 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____3476) with
| true -> begin
(

let uu____3477 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3478 = (FStar_Syntax_Print.term_to_string phi)
in (

let uu____3479 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____3477 uu____3478 uu____3479))))
end
| uu____3480 -> begin
()
end));
(

let uu____3481 = (FStar_Syntax_Util.type_u ())
in (match (uu____3481) with
| (t_phi, uu____3488) -> begin
(

let uu____3489 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (uu____3489) with
| (phi, uu____3497, f2) -> begin
(

let e = (

let uu___98_3502 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = uu___98_3502.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___98_3502.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___98_3502.FStar_Syntax_Syntax.vars})
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____3521 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____3521))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____3530) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in ((

let uu____3555 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3555) with
| true -> begin
(

let uu____3556 = (FStar_Syntax_Print.term_to_string (

let uu___99_3557 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = uu___99_3557.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___99_3557.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___99_3557.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____3556))
end
| uu____3575 -> begin
()
end));
(

let uu____3576 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3576) with
| (bs, body) -> begin
(tc_abs env top bs body)
end));
))
end
| uu____3584 -> begin
(

let uu____3585 = (

let uu____3586 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____3587 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____3586 uu____3587)))
in (failwith uu____3585))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (uu____3593) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (uu____3594, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (uu____3600, Some (uu____3601)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____3609) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (uu____3613) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (uu____3614) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____3615) -> begin
FStar_TypeChecker_Common.t_range
end
| uu____3616 -> begin
(Prims.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____3627) -> begin
(

let uu____3634 = (FStar_Syntax_Util.type_u ())
in (match (uu____3634) with
| (k, u) -> begin
(

let uu____3642 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3642) with
| (t, uu____3650, g) -> begin
(

let uu____3652 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((uu____3652), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____3654) -> begin
(

let uu____3661 = (FStar_Syntax_Util.type_u ())
in (match (uu____3661) with
| (k, u) -> begin
(

let uu____3669 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3669) with
| (t, uu____3677, g) -> begin
(

let uu____3679 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((uu____3679), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let head = (match (c.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
head
end
| us -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((head), (us))))) None c0.FStar_Syntax_Syntax.pos)
end)
in (

let tc = (

let uu____3695 = (

let uu____3696 = (

let uu____3697 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____3697)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head uu____3696))
in (uu____3695 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____3702 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____3702) with
| (tc, uu____3710, f) -> begin
(

let uu____3712 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3712) with
| (head, args) -> begin
(

let comp_univs = (

let uu____3742 = (

let uu____3743 = (FStar_Syntax_Subst.compress head)
in uu____3743.FStar_Syntax_Syntax.n)
in (match (uu____3742) with
| FStar_Syntax_Syntax.Tm_uinst (uu____3746, us) -> begin
us
end
| uu____3752 -> begin
[]
end))
in (

let uu____3753 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3753) with
| (uu____3766, args) -> begin
(

let uu____3782 = (

let uu____3794 = (FStar_List.hd args)
in (

let uu____3803 = (FStar_List.tl args)
in ((uu____3794), (uu____3803))))
in (match (uu____3782) with
| (res, args) -> begin
(

let uu____3845 = (

let uu____3850 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___79_3860 -> (match (uu___79_3860) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____3866 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3866) with
| (env, uu____3873) -> begin
(

let uu____3876 = (tc_tot_or_gtot_term env e)
in (match (uu____3876) with
| (e, uu____3883, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____3850 FStar_List.unzip))
in (match (uu____3845) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let uu___100_3906 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___100_3906.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = uu___100_3906.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____3910 = (FStar_TypeChecker_Util.effect_repr env c u)
in (match (uu____3910) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____3913 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (uu____3913))))))
end))
end))
end)))
end))
end)))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (uu____3921) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let uu____3924 = (aux u)
in FStar_Syntax_Syntax.U_succ (uu____3924))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____3927 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____3927))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____3930 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____3931 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____3931 Prims.snd))
end
| uu____3936 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (

let uu____3957 = (

let uu____3958 = (

let uu____3961 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((uu____3961), (top.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____3958))
in (Prims.raise uu____3957)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun uu____4019 bs bs_expected -> (match (uu____4019) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
((match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(

let uu____4116 = (

let uu____4117 = (

let uu____4120 = (

let uu____4121 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____4121))
in (

let uu____4122 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((uu____4120), (uu____4122))))
in FStar_Errors.Error (uu____4117))
in (Prims.raise uu____4116))
end
| uu____4123 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____4127 = (

let uu____4130 = (

let uu____4131 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in uu____4131.FStar_Syntax_Syntax.n)
in (match (uu____4130) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____4136 -> begin
((

let uu____4138 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____4138) with
| true -> begin
(

let uu____4139 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" uu____4139))
end
| uu____4140 -> begin
()
end));
(

let uu____4141 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (uu____4141) with
| (t, uu____4148, g1) -> begin
(

let g2 = (

let uu____4151 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4152 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard uu____4151 "Type annotation on parameter incompatible with the expected type" uu____4152)))
in (

let g = (

let uu____4154 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____4154))
in ((t), (g))))
end));
)
end))
in (match (uu____4127) with
| (t, g) -> begin
(

let hd = (

let uu___101_4170 = hd
in {FStar_Syntax_Syntax.ppname = uu___101_4170.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___101_4170.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (

let uu____4179 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected uu____4179))
in (aux ((env), ((b)::out), (g), (subst)) bs bs_expected))))))
end)));
)
end
| (rest, []) -> begin
((env), ((FStar_List.rev out)), (Some (FStar_Util.Inl (rest))), (g), (subst))
end
| ([], rest) -> begin
((env), ((FStar_List.rev out)), (Some (FStar_Util.Inr (rest))), (g), (subst))
end)
end))
in (aux ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs bs_expected)))
in (

let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
((match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4275 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____4279 = (tc_binders env bs)
in (match (uu____4279) with
| (bs, envbody, g, uu____4298) -> begin
(

let uu____4299 = (

let uu____4304 = (

let uu____4305 = (FStar_Syntax_Subst.compress body)
in uu____4305.FStar_Syntax_Syntax.n)
in (match (uu____4304) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), uu____4314) -> begin
(

let uu____4333 = (tc_comp envbody c)
in (match (uu____4333) with
| (c, uu____4342, g') -> begin
(

let uu____4344 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (uu____4344)))
end))
end
| uu____4346 -> begin
((None), (body), (g))
end))
in (match (uu____4299) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end));
)
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (

let uu____4396 = (

let uu____4397 = (FStar_Syntax_Subst.compress t)
in uu____4397.FStar_Syntax_Syntax.n)
in (match (uu____4396) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
((match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4428 -> begin
(failwith "Impossible")
end);
(

let uu____4432 = (tc_binders env bs)
in (match (uu____4432) with
| (bs, envbody, g, uu____4452) -> begin
(

let uu____4453 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____4453) with
| (envbody, uu____4470) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____4481) -> begin
(

let uu____4486 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (uu____4486) with
| (uu____4511, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____4547 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____4547) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun uu____4608 c_expected -> (match (uu____4608) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(

let uu____4669 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (uu____4669)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____4686 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total uu____4686))
in (

let uu____4687 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (uu____4687))))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (match ((FStar_Syntax_Util.is_named_tot c)) with
| true -> begin
(

let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____4728 = (check_binders env more_bs bs_expected)
in (match (uu____4728) with
| (env, bs', more, guard', subst) -> begin
(

let uu____4767 = (

let uu____4783 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (uu____4783), (subst)))
in (handle_more uu____4767 c_expected))
end))
end
| uu____4793 -> begin
(

let uu____4794 = (

let uu____4795 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" uu____4795))
in (fail uu____4794 t))
end))
end
| uu____4803 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end))
end)
end))
in (

let uu____4811 = (check_binders env bs bs_expected)
in (handle_more uu____4811 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let uu___102_4849 = envbody
in {FStar_TypeChecker_Env.solver = uu___102_4849.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___102_4849.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___102_4849.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___102_4849.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___102_4849.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___102_4849.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___102_4849.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___102_4849.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___102_4849.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___102_4849.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___102_4849.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___102_4849.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___102_4849.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___102_4849.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___102_4849.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___102_4849.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___102_4849.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___102_4849.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___102_4849.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___102_4849.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___102_4849.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___102_4849.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___102_4849.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____4863 uu____4864 -> (match (((uu____4863), (uu____4864))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let uu____4889 = (

let uu____4893 = (

let uu____4894 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____4894 Prims.fst))
in (tc_term uu____4893 t))
in (match (uu____4889) with
| (t, uu____4906, uu____4907) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____4914 = (FStar_Syntax_Syntax.mk_binder (

let uu___103_4915 = x
in {FStar_Syntax_Syntax.ppname = uu___103_4915.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___103_4915.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____4914)::letrec_binders)
end
| uu____4916 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let uu____4919 = (check_actuals_against_formals env bs bs_expected)
in (match (uu____4919) with
| (envbody, bs, g, c) -> begin
(

let uu____4949 = (

let uu____4953 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____4953) with
| true -> begin
(mk_letrec_env envbody bs c)
end
| uu____4957 -> begin
((envbody), ([]))
end))
in (match (uu____4949) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| uu____4986 -> begin
(match ((not (norm))) with
| true -> begin
(

let uu____4999 = (unfold_whnf env t)
in (as_function_typ true uu____4999))
end
| uu____5000 -> begin
(

let uu____5001 = (expected_function_typ env None body)
in (match (uu____5001) with
| (uu____5025, bs, uu____5027, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end)
end)))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____5048 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____5048) with
| (env, topt) -> begin
((

let uu____5060 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5060) with
| true -> begin
(

let uu____5061 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____5061 (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____5063 -> begin
"false"
end)))
end
| uu____5064 -> begin
()
end));
(

let uu____5065 = (expected_function_typ env topt body)
in (match (uu____5065) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let uu____5095 = (tc_term (

let uu___104_5099 = envbody
in {FStar_TypeChecker_Env.solver = uu___104_5099.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___104_5099.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___104_5099.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___104_5099.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___104_5099.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___104_5099.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___104_5099.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___104_5099.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___104_5099.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___104_5099.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___104_5099.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___104_5099.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___104_5099.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___104_5099.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___104_5099.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___104_5099.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___104_5099.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___104_5099.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___104_5099.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___104_5099.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___104_5099.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___104_5099.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (uu____5095) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in ((

let uu____5108 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))
in (match (uu____5108) with
| true -> begin
(

let uu____5109 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (

let uu____5118 = (

let uu____5119 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____5119))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" uu____5109 uu____5118)))
end
| uu____5120 -> begin
()
end));
(

let uu____5121 = (

let uu____5125 = (

let uu____5128 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (uu____5128)))
in (check_expected_effect (

let uu___105_5133 = envbody
in {FStar_TypeChecker_Env.solver = uu___105_5133.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___105_5133.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___105_5133.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___105_5133.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___105_5133.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___105_5133.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___105_5133.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___105_5133.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___105_5133.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___105_5133.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___105_5133.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___105_5133.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___105_5133.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___105_5133.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___105_5133.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___105_5133.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___105_5133.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___105_5133.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___105_5133.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___105_5133.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___105_5133.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___105_5133.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___105_5133.FStar_TypeChecker_Env.qname_and_index}) c_opt uu____5125))
in (match (uu____5121) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = (

let uu____5142 = (env.FStar_TypeChecker_Env.top_level || (

let uu____5143 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____5143))))
in (match (uu____5142) with
| true -> begin
(

let uu____5144 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____5144))
end
| uu____5145 -> begin
(

let guard = (

let uu____5147 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) uu____5147))
in guard)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (

let uu____5154 = (

let uu____5161 = (

let uu____5167 = (FStar_All.pipe_right (FStar_Util.dflt cbody c_opt) FStar_Syntax_Util.lcomp_of_comp)
in (FStar_All.pipe_right uu____5167 (fun _0_29 -> FStar_Util.Inl (_0_29))))
in Some (uu____5161))
in (FStar_Syntax_Util.abs bs body uu____5154))
in (

let uu____5181 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5196) -> begin
((e), (t), (guard))
end
| uu____5204 -> begin
(

let uu____5205 = (match (use_teq) with
| true -> begin
(

let uu____5210 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (uu____5210)))
end
| uu____5211 -> begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end)
in (match (uu____5205) with
| (e, guard') -> begin
(

let uu____5217 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (uu____5217)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (uu____5181) with
| (e, tfun, guard) -> begin
(

let c = (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____5229 -> begin
(FStar_TypeChecker_Util.return_value env tfun e)
end)
in (

let uu____5230 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (uu____5230) with
| (c, g) -> begin
((e), (c), (g))
end)))
end))))))
end));
))
end))
end));
)
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in ((

let uu____5266 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5266) with
| true -> begin
(

let uu____5267 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (

let uu____5268 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____5267 uu____5268)))
end
| uu____5269 -> begin
()
end));
(

let monadic_application = (fun uu____5310 subst arg_comps_rev arg_rets guard fvs bs -> (match (uu____5310) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___106_5351 = cres
in {FStar_Syntax_Syntax.eff_name = uu___106_5351.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___106_5351.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___106_5351.FStar_Syntax_Syntax.comp})
in (

let uu____5352 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun uu___80_5379 -> (match (uu___80_5379) with
| (uu____5388, uu____5389, FStar_Util.Inl (uu____5390)) -> begin
false
end
| (uu____5401, uu____5402, FStar_Util.Inr (c)) -> begin
(

let uu____5412 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (not (uu____5412)))
end)))))
in (

let cres = (match (refine_with_equality) with
| true -> begin
(

let uu____5414 = ((FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets)) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env uu____5414 cres))
end
| uu____5423 -> begin
((

let uu____5425 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5425) with
| true -> begin
(

let uu____5426 = (FStar_Syntax_Print.term_to_string head)
in (

let uu____5427 = (FStar_Syntax_Print.lcomp_to_string cres)
in (

let uu____5428 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" uu____5426 uu____5427 uu____5428))))
end
| uu____5429 -> begin
()
end));
cres;
)
end)
in ((cres), (g))))))
end
| uu____5430 -> begin
(

let g = (

let uu____5435 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right uu____5435 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (

let uu____5436 = (

let uu____5437 = (

let uu____5440 = (

let uu____5441 = (

let uu____5442 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs uu____5442))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) uu____5441))
in (FStar_Syntax_Syntax.mk_Total uu____5440))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5437))
in ((uu____5436), (g))))
end)
in (match (uu____5352) with
| (cres, guard) -> begin
((

let uu____5453 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5453) with
| true -> begin
(

let uu____5454 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____5454))
end
| uu____5455 -> begin
()
end));
(

let comp = (FStar_List.fold_left (fun out_c uu____5470 -> (match (uu____5470) with
| ((e, q), x, c) -> begin
(match (c) with
| FStar_Util.Inl (eff_name, arg_typ) -> begin
out_c
end
| FStar_Util.Inr (c) -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c ((x), (out_c)))
end)
end)) cres arg_comps_rev)
in (

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead ((None), (comp)))
in (

let shortcuts_evaluation_order = (

let uu____5516 = (

let uu____5517 = (FStar_Syntax_Subst.compress head)
in uu____5517.FStar_Syntax_Syntax.n)
in (match (uu____5516) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Or))
end
| uu____5521 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args = (FStar_List.fold_left (fun args uu____5535 -> (match (uu____5535) with
| (arg, uu____5547, uu____5548) -> begin
(arg)::args
end)) [] arg_comps_rev)
in (

let app = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_lift env app cres.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ))))
end
| uu____5567 -> begin
(

let uu____5568 = (

let map_fun = (fun uu____5607 -> (match (uu____5607) with
| ((e, q), uu____5631, c0) -> begin
(match (c0) with
| FStar_Util.Inl (uu____5656) -> begin
((None), (((e), (q))))
end
| FStar_Util.Inr (c) when (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) -> begin
((None), (((e), (q))))
end
| FStar_Util.Inr (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None c.FStar_Syntax_Syntax.res_typ)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____5699 = (

let uu____5702 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____5702), (q)))
in ((Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e)))), (uu____5699)))))
end)
end))
in (

let uu____5720 = (

let uu____5734 = (

let uu____5747 = (

let uu____5759 = (

let uu____5768 = (FStar_Syntax_Syntax.as_arg head)
in ((uu____5768), (None), (FStar_Util.Inr (chead))))
in (uu____5759)::arg_comps_rev)
in (FStar_List.map map_fun uu____5747))
in (FStar_All.pipe_left FStar_List.split uu____5734))
in (match (uu____5720) with
| (lifted_args, reverse_args) -> begin
(

let uu____5877 = (

let uu____5878 = (FStar_List.hd reverse_args)
in (Prims.fst uu____5878))
in (

let uu____5883 = (

let uu____5887 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____5887))
in ((lifted_args), (uu____5877), (uu____5883))))
end)))
in (match (uu____5568) with
| (lifted_args, head, args) -> begin
(

let app = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_lift env app cres.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
in (

let app = (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___81_5955 -> (match (uu___81_5955) with
| None -> begin
e
end
| Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1)
in (

let letbinding = (

let uu____5997 = (

let uu____6000 = (

let uu____6001 = (

let uu____6009 = (

let uu____6010 = (

let uu____6011 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6011)::[])
in (FStar_Syntax_Subst.close uu____6010 e))
in ((((false), ((lb)::[]))), (uu____6009)))
in FStar_Syntax_Syntax.Tm_let (uu____6001))
in (FStar_Syntax_Syntax.mk uu____6000))
in (uu____5997 None e.FStar_Syntax_Syntax.pos))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp.FStar_Syntax_Syntax.res_typ)))))))) None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app lifted_args)))))
end))
end)
in (

let uu____6045 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (uu____6045) with
| (comp, g) -> begin
((app), (comp), (g))
end))))));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____6103 bs args -> (match (uu____6103) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (uu____6198))))::rest, ((uu____6200, None))::uu____6201) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let uu____6238 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (uu____6238) with
| (varg, uu____6249, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (

let uu____6262 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____6262)))
in (

let uu____6263 = (

let uu____6285 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (FStar_Util.Inl (((FStar_Syntax_Const.effect_Tot_lid), (t))))))::outargs), ((arg)::arg_rets), (uu____6285), (fvs)))
in (tc_args head_info uu____6263 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| uu____6376 -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___107_6383 = x
in {FStar_Syntax_Syntax.ppname = uu___107_6383.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_6383.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____6385 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____6385) with
| true -> begin
(

let uu____6386 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____6386))
end
| uu____6387 -> begin
()
end));
(

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let uu___108_6391 = env
in {FStar_TypeChecker_Env.solver = uu___108_6391.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___108_6391.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___108_6391.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___108_6391.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___108_6391.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___108_6391.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___108_6391.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___108_6391.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___108_6391.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___108_6391.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___108_6391.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___108_6391.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___108_6391.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___108_6391.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___108_6391.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___108_6391.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___108_6391.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___108_6391.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___108_6391.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___108_6391.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___108_6391.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___108_6391.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___108_6391.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____6393 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6393) with
| true -> begin
(

let uu____6394 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____6395 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6396 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____6394 uu____6395 uu____6396))))
end
| uu____6397 -> begin
()
end));
(

let uu____6398 = (tc_term env e)
in (match (uu____6398) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in (

let uu____6414 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____6414) with
| true -> begin
(

let subst = (

let uu____6419 = (FStar_List.hd bs)
in (maybe_extend_subst subst uu____6419 e))
in (tc_args head_info ((subst), ((((arg), (None), (FStar_Util.Inl (((c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ))))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____6474 -> begin
(

let uu____6475 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name)
in (match (uu____6475) with
| true -> begin
(

let subst = (

let uu____6480 = (FStar_List.hd bs)
in (maybe_extend_subst subst uu____6480 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____6525 -> begin
(

let uu____6526 = (

let uu____6527 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder uu____6527))
in (match (uu____6526) with
| true -> begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (

let uu____6536 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6536))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end
| uu____6573 -> begin
(

let uu____6574 = (

let uu____6596 = (

let uu____6598 = (

let uu____6599 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____6599))
in (uu____6598)::arg_rets)
in ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), (uu____6596), (g), ((x)::fvs)))
in (tc_args head_info uu____6574 rest rest'))
end))
end))
end))))
end));
))));
)));
)
end
| (uu____6636, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____6657) -> begin
(

let uu____6687 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (uu____6687) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (

let uu____6710 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____6710 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let uu____6726 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (uu____6726) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in ((

let uu____6740 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6740) with
| true -> begin
(

let uu____6741 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" uu____6741))
end
| uu____6742 -> begin
()
end));
(tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args);
))
end))
end
| uu____6771 when (not (norm)) -> begin
(

let uu____6772 = (unfold_whnf env tres)
in (aux true uu____6772))
end
| uu____6773 -> begin
(

let uu____6774 = (

let uu____6775 = (

let uu____6778 = (

let uu____6779 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____6780 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" uu____6779 uu____6780)))
in (

let uu____6784 = (FStar_Syntax_Syntax.argpos arg)
in ((uu____6778), (uu____6784))))
in FStar_Errors.Error (uu____6775))
in (Prims.raise uu____6774))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (

let uu____6800 = (

let uu____6801 = (FStar_Syntax_Util.unrefine tf)
in uu____6801.FStar_Syntax_Syntax.n)
in (match (uu____6800) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let uu____6877 = (tc_term env e)
in (match (uu____6877) with
| (e, c, g_e) -> begin
(

let uu____6890 = (tc_args env tl)
in (match (uu____6890) with
| (args, comps, g_rest) -> begin
(

let uu____6912 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____6912)))
end))
end))
end))
in (

let uu____6923 = (tc_args env args)
in (match (uu____6923) with
| (args, comps, g_args) -> begin
(

let bs = (

let uu____6948 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____6968 -> (match (uu____6968) with
| (uu____6976, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____6948))
in (

let ml_or_tot = (

let uu____6986 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)
in (match (uu____6986) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| uu____6994 -> begin
FStar_Syntax_Util.ml_comp
end))
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(

let uu____7006 = (

let uu____7007 = (FStar_Syntax_Subst.compress t)
in uu____7007.FStar_Syntax_Syntax.n)
in (match (uu____7006) with
| FStar_Syntax_Syntax.Tm_type (uu____7014) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| uu____7017 -> begin
ml_or_tot
end))
end)
in (

let cres = (

let uu____7019 = (

let uu____7020 = (

let uu____7021 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7021 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____7020))
in (ml_or_tot uu____7019 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____7030 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____7030) with
| true -> begin
(

let uu____7031 = (FStar_Syntax_Print.term_to_string head)
in (

let uu____7032 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____7033 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____7031 uu____7032 uu____7033))))
end
| uu____7034 -> begin
()
end));
(

let uu____7036 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____7036));
(

let comp = (

let uu____7038 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____7043 out -> (match (uu____7043) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____7038))
in (

let uu____7052 = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let uu____7059 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____7052), (comp), (uu____7059)))));
))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7074 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7074) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| uu____7117 -> begin
(match ((not (norm))) with
| true -> begin
(

let uu____7123 = (unfold_whnf env tf)
in (check_function_app true uu____7123))
end
| uu____7124 -> begin
(

let uu____7125 = (

let uu____7126 = (

let uu____7129 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((uu____7129), (head.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____7126))
in (Prims.raise uu____7125))
end)
end)))
in (

let uu____7135 = (

let uu____7136 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____7136))
in (check_function_app false uu____7135)))));
)))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let uu____7182 = (FStar_List.fold_left2 (fun uu____7195 uu____7196 uu____7197 -> (match (((uu____7195), (uu____7196), (uu____7197))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((aq <> aq')) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7240 -> begin
()
end);
(

let uu____7241 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____7241) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (

let uu____7253 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____7253 g))
in (

let ghost = (ghost || ((

let uu____7255 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____7255))) && (

let uu____7256 = (FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)
in (not (uu____7256)))))
in (

let uu____7257 = (

let uu____7263 = (

let uu____7269 = (FStar_Syntax_Syntax.as_arg e)
in (uu____7269)::[])
in (FStar_List.append seen uu____7263))
in (

let uu____7274 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((uu____7257), (uu____7274), (ghost)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____7182) with
| (args, guard, ghost) -> begin
(

let e = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = (match (ghost) with
| true -> begin
(

let uu____7303 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____7303 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____7304 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____7305 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (uu____7305) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| uu____7317 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let uu____7339 = (FStar_Syntax_Subst.open_branch branch)
in (match (uu____7339) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____7365 = branch
in (match (uu____7365) with
| (cpat, uu____7385, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let uu____7427 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (uu____7427) with
| (pat_bvs, exps, p) -> begin
((

let uu____7449 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7449) with
| true -> begin
(

let uu____7450 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____7451 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____7450 uu____7451)))
end
| uu____7452 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let uu____7454 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____7454) with
| (env1, uu____7467) -> begin
(

let env1 = (

let uu___109_7471 = env1
in {FStar_TypeChecker_Env.solver = uu___109_7471.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___109_7471.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___109_7471.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___109_7471.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___109_7471.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___109_7471.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___109_7471.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___109_7471.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___109_7471.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___109_7471.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___109_7471.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___109_7471.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___109_7471.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___109_7471.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___109_7471.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___109_7471.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___109_7471.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___109_7471.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___109_7471.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___109_7471.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___109_7471.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___109_7471.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___109_7471.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let uu____7473 = (

let uu____7478 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> ((

let uu____7490 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7490) with
| true -> begin
(

let uu____7491 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7492 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____7491 uu____7492)))
end
| uu____7493 -> begin
()
end));
(

let uu____7494 = (tc_term env1 e)
in (match (uu____7494) with
| (e, lc, g) -> begin
((

let uu____7504 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7504) with
| true -> begin
(

let uu____7505 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____7506 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" uu____7505 uu____7506)))
end
| uu____7507 -> begin
()
end));
(

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let uu____7510 = (

let uu____7511 = (FStar_TypeChecker_Rel.discharge_guard env (

let uu___110_7512 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___110_7512.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___110_7512.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___110_7512.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right uu____7511 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (

let uu____7526 = (

let uu____7528 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right uu____7528 (FStar_List.map (fun uu____7552 -> (match (uu____7552) with
| (u, uu____7557) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right uu____7526 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____7570 = (

let uu____7571 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____7571))
in (match (uu____7570) with
| true -> begin
(

let unresolved = (

let uu____7578 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right uu____7578 FStar_Util.set_elements))
in (

let uu____7592 = (

let uu____7593 = (

let uu____7596 = (

let uu____7597 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (

let uu____7598 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____7599 = (

let uu____7600 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____7612 -> (match (uu____7612) with
| (u, uu____7620) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____7600 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____7597 uu____7598 uu____7599))))
in ((uu____7596), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____7593))
in (Prims.raise uu____7592)))
end
| uu____7633 -> begin
()
end));
(

let uu____7635 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7635) with
| true -> begin
(

let uu____7636 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____7636))
end
| uu____7637 -> begin
()
end));
((e), (e'));
))))))));
)
end));
))))
in (FStar_All.pipe_right uu____7478 FStar_List.unzip))
in (match (uu____7473) with
| (exps, norm_exps) -> begin
(

let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in ((p), (pat_bvs), (pat_env), (exps), (norm_exps)))
end))))
end)));
)
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let uu____7667 = (

let uu____7671 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____7671 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____7667) with
| (scrutinee_env, uu____7684) -> begin
(

let uu____7687 = (tc_pat true pat_t pattern)
in (match (uu____7687) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let uu____7715 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
(

let uu____7730 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____7730) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7737 -> begin
(

let uu____7738 = (

let uu____7742 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term uu____7742 e))
in (match (uu____7738) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end))
end)
in (match (uu____7715) with
| (when_clause, g_when) -> begin
(

let uu____7762 = (tc_term pat_env branch_exp)
in (match (uu____7762) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____7787 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____7787))
end)
in (

let uu____7797 = (

let eqs = (

let uu____7805 = (

let uu____7806 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7806)))
in (match (uu____7805) with
| true -> begin
None
end
| uu____7812 -> begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| uu____7832 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(

let uu____7852 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____7852))
end))
end))) None))
end))
in (

let uu____7864 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (uu____7864) with
| (c, g_branch) -> begin
(

let uu____7874 = (match (((eqs), (when_condition))) with
| uu____7885 when (

let uu____7894 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7894))) -> begin
((c), (g_when))
end
| (None, None) -> begin
((c), (g_when))
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (

let uu____7920 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (

let uu____7921 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____7920), (uu____7921))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____7940 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____7940))
in (

let uu____7941 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (

let uu____7942 = (

let uu____7943 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____7943 g_when))
in ((uu____7941), (uu____7942))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____7959 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((uu____7959), (g_when)))))
end)
in (match (uu____7874) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (

let uu____7967 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (

let uu____7968 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((uu____7967), (uu____7968), (g_branch)))))
end))
end)))
in (match (uu____7797) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let uu____7981 = (

let uu____7982 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7982)))
in (match (uu____7981) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____7983 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> (

let uu____8015 = (

let uu____8016 = (

let uu____8017 = (

let uu____8019 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____8019))
in (FStar_List.length uu____8017))
in (uu____8016 > (Prims.parse_int "1")))
in (match (uu____8015) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____8029 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____8029) with
| None -> begin
[]
end
| uu____8040 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational None)
in (

let disc = (

let uu____8048 = (

let uu____8049 = (

let uu____8050 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (uu____8050)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____8049))
in (uu____8048 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (

let uu____8055 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (uu____8055)::[])))
end)))
end
| uu____8062 -> begin
[]
end)))
in (

let fail = (fun uu____8071 -> (

let uu____8072 = (

let uu____8073 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (

let uu____8074 = (FStar_Syntax_Print.term_to_string pat_exp)
in (

let uu____8075 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____8073 uu____8074 uu____8075))))
in (failwith uu____8072)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____8096) -> begin
(head_constructor t)
end
| uu____8102 -> begin
(fail ())
end))
in (

let pat_exp = (

let uu____8105 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right uu____8105 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____8121) -> begin
(

let uu____8122 = (

let uu____8125 = (

let uu____8126 = (

let uu____8127 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (

let uu____8128 = (

let uu____8130 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (uu____8130)::[])
in (uu____8127)::uu____8128))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq uu____8126))
in (uu____8125 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (uu____8122)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in (

let uu____8146 = (

let uu____8147 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____8147)))
in (match (uu____8146) with
| true -> begin
[]
end
| uu____8153 -> begin
(

let uu____8154 = (head_constructor pat_exp)
in (discriminate scrutinee_tm uu____8154))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in (

let uu____8181 = (

let uu____8182 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____8182)))
in (match (uu____8181) with
| true -> begin
[]
end
| uu____8188 -> begin
(

let sub_term_guards = (

let uu____8191 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____8207 -> (match (uu____8207) with
| (ei, uu____8214) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____8224 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____8224) with
| None -> begin
[]
end
| uu____8231 -> begin
(

let sub_term = (

let uu____8238 = (

let uu____8239 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (

let uu____8244 = (

let uu____8245 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (uu____8245)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____8239 uu____8244)))
in (uu____8238 None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____8191 FStar_List.flatten))
in (

let uu____8257 = (discriminate scrutinee_tm f)
in (FStar_List.append uu____8257 sub_term_guards)))
end)))
end
| uu____8265 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> (

let uu____8277 = (

let uu____8278 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8278)))
in (match (uu____8277) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end
| uu____8279 -> begin
(

let t = (

let uu____8281 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____8281))
in (

let uu____8284 = (FStar_Syntax_Util.type_u ())
in (match (uu____8284) with
| (k, uu____8288) -> begin
(

let uu____8289 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____8289) with
| (t, uu____8294, uu____8295) -> begin
t
end))
end)))
end)))
in (

let branch_guard = (

let uu____8297 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right uu____8297 FStar_Syntax_Util.mk_disj_l))
in (

let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
end))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in ((

let uu____8314 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8314) with
| true -> begin
(

let uu____8315 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____8315))
end
| uu____8316 -> begin
()
end));
(

let uu____8317 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((uu____8317), (branch_guard), (c), (guard)));
)))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let uu____8335 = (check_let_bound_def true env lb)
in (match (uu____8335) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let uu____8349 = (match ((annotated && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
((g1), (e1), (univ_vars), (c1))
end
| uu____8358 -> begin
(

let g1 = (

let uu____8360 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right uu____8360 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____8362 = (

let uu____8367 = (

let uu____8373 = (

let uu____8378 = (

let uu____8386 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____8386)))
in (uu____8378)::[])
in (FStar_TypeChecker_Util.generalize env uu____8373))
in (FStar_List.hd uu____8367))
in (match (uu____8362) with
| (uu____8415, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end)
in (match (uu____8349) with
| (g1, e1, univ_vars, c1) -> begin
(

let uu____8426 = (

let uu____8431 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____8431) with
| true -> begin
(

let uu____8436 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (uu____8436) with
| (ok, c1) -> begin
(match (ok) with
| true -> begin
((e2), (c1))
end
| uu____8451 -> begin
((

let uu____8453 = (FStar_Options.warn_top_level_effects ())
in (match (uu____8453) with
| true -> begin
(

let uu____8454 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.warn uu____8454 FStar_TypeChecker_Err.top_level_effect))
end
| uu____8455 -> begin
()
end));
(

let uu____8456 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))))) None e2.FStar_Syntax_Syntax.pos)
in ((uu____8456), (c1)));
)
end)
end))
end
| uu____8471 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let c = (

let uu____8474 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right uu____8474 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c)));
)
end))
in (match (uu____8426) with
| (e2, c1) -> begin
(

let cres = (

let uu____8491 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8491))
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (

let uu____8502 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((uu____8502), (cres), (FStar_TypeChecker_Rel.trivial_guard))));
))
end))
end))
end))
end
| uu____8521 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let uu___111_8542 = env
in {FStar_TypeChecker_Env.solver = uu___111_8542.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_8542.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_8542.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_8542.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_8542.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_8542.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_8542.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_8542.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_8542.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_8542.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_8542.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_8542.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_8542.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___111_8542.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_8542.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_8542.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_8542.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___111_8542.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___111_8542.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___111_8542.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_8542.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_8542.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_8542.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____8543 = (

let uu____8549 = (

let uu____8550 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____8550 Prims.fst))
in (check_let_bound_def false uu____8549 lb))
in (match (uu____8543) with
| (e1, uu____8562, c1, g1, annotated) -> begin
(

let x = (

let uu___112_8567 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___112_8567.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_8567.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____8568 = (

let uu____8571 = (

let uu____8572 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____8572)::[])
in (FStar_Syntax_Subst.open_term uu____8571 e2))
in (match (uu____8568) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let uu____8584 = (

let uu____8588 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term uu____8588 e2))
in (match (uu____8584) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let e = (

let uu____8603 = (

let uu____8606 = (

let uu____8607 = (

let uu____8615 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (uu____8615)))
in FStar_Syntax_Syntax.Tm_let (uu____8607))
in (FStar_Syntax_Syntax.mk uu____8606))
in (uu____8603 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____8630 = (

let uu____8631 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ uu____8631 e1))
in (FStar_All.pipe_left (fun _0_32 -> FStar_TypeChecker_Common.NonTrivial (_0_32)) uu____8630))
in (

let g2 = (

let uu____8637 = (

let uu____8638 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____8638 g2))
in (FStar_TypeChecker_Rel.close_guard xb uu____8637))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (

let uu____8640 = (

let uu____8641 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome uu____8641))
in (match (uu____8640) with
| true -> begin
(

let tt = (

let uu____8647 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right uu____8647 FStar_Option.get))
in ((

let uu____8651 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____8651) with
| true -> begin
(

let uu____8652 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____8653 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____8652 uu____8653)))
end
| uu____8654 -> begin
()
end));
((e), (cres), (guard));
))
end
| uu____8655 -> begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____8658 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____8658) with
| true -> begin
(

let uu____8659 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____8660 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____8659 uu____8660)))
end
| uu____8661 -> begin
()
end));
((e), ((

let uu___113_8662 = cres
in {FStar_Syntax_Syntax.eff_name = uu___113_8662.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___113_8662.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___113_8662.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____8663 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8684 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8684) with
| (lbs, e2) -> begin
(

let uu____8695 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8695) with
| (env0, topt) -> begin
(

let uu____8706 = (build_let_rec_env true env0 lbs)
in (match (uu____8706) with
| (lbs, rec_env) -> begin
(

let uu____8717 = (check_let_recs rec_env lbs)
in (match (uu____8717) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (

let uu____8729 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right uu____8729 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (

let uu____8733 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____8733 (fun _0_33 -> Some (_0_33))))
in (

let lbs = (match ((not (env.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (match ((lb.FStar_Syntax_Syntax.lbunivs = [])) with
| true -> begin
lb
end
| uu____8749 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end))))
end
| uu____8750 -> begin
(

let ecs = (

let uu____8757 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____8779 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____8779))))))
in (FStar_TypeChecker_Util.generalize env uu____8757))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____8799 -> (match (uu____8799) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (

let uu____8824 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8824))
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let uu____8833 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____8833) with
| (lbs, e2) -> begin
(

let uu____8844 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____8859 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((uu____8844), (cres), (uu____8859))))
end));
)))))
end))
end))
end))
end))
end
| uu____8862 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8883 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8883) with
| (lbs, e2) -> begin
(

let uu____8894 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8894) with
| (env0, topt) -> begin
(

let uu____8905 = (build_let_rec_env false env0 lbs)
in (match (uu____8905) with
| (lbs, rec_env) -> begin
(

let uu____8916 = (check_let_recs rec_env lbs)
in (match (uu____8916) with
| (lbs, g_lbs) -> begin
(

let uu____8927 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let uu___114_8938 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___114_8938.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_8938.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let uu___115_8940 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___115_8940.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___115_8940.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___115_8940.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___115_8940.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (uu____8927) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____8957 = (tc_term env e2)
in (match (uu____8957) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___116_8971 = cres
in {FStar_Syntax_Syntax.eff_name = uu___116_8971.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___116_8971.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___116_8971.FStar_Syntax_Syntax.comp})
in (

let uu____8972 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____8972) with
| (lbs, e2) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (uu____9001) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let uu___117_9006 = cres
in {FStar_Syntax_Syntax.eff_name = uu___117_9006.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___117_9006.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___117_9006.FStar_Syntax_Syntax.comp})
in ((e), (cres), (guard))))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| uu____9009 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let uu____9025 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____9025) with
| (uu____9031, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let uu____9042 = (FStar_List.fold_left (fun uu____9049 lb -> (match (uu____9049) with
| (lbs, env) -> begin
(

let uu____9061 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (uu____9061) with
| (univ_vars, t, check_t) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t = (match ((not (check_t))) with
| true -> begin
t
end
| uu____9074 -> begin
(

let uu____9075 = (

let uu____9079 = (

let uu____9080 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst uu____9080))
in (tc_check_tot_or_gtot_term (

let uu___118_9085 = env0
in {FStar_TypeChecker_Env.solver = uu___118_9085.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___118_9085.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___118_9085.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___118_9085.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___118_9085.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___118_9085.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___118_9085.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___118_9085.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___118_9085.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___118_9085.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___118_9085.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___118_9085.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___118_9085.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___118_9085.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___118_9085.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___118_9085.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___118_9085.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___118_9085.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___118_9085.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___118_9085.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___118_9085.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___118_9085.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___118_9085.FStar_TypeChecker_Env.qname_and_index}) t uu____9079))
in (match (uu____9075) with
| (t, uu____9087, g) -> begin
(

let g = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((

let uu____9091 = (FStar_TypeChecker_Rel.discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore uu____9091));
(norm env0 t);
))
end))
end)
in (

let env = (

let uu____9093 = ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env))
in (match (uu____9093) with
| true -> begin
(

let uu___119_9094 = env
in {FStar_TypeChecker_Env.solver = uu___119_9094.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_9094.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_9094.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_9094.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_9094.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_9094.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_9094.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_9094.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_9094.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_9094.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_9094.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_9094.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_9094.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_9094.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_9094.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_9094.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_9094.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___119_9094.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___119_9094.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___119_9094.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_9094.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_9094.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_9094.FStar_TypeChecker_Env.qname_and_index})
end
| uu____9101 -> begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end))
in (

let lb = (

let uu___120_9104 = lb
in {FStar_Syntax_Syntax.lbname = uu___120_9104.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___120_9104.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____9042) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____9118 = (

let uu____9123 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____9134 = (

let uu____9138 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____9138 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____9134) with
| (e, c, g) -> begin
((

let uu____9145 = (

let uu____9146 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____9146)))
in (match (uu____9145) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____9147 -> begin
()
end));
(

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g)));
)
end)))))
in (FStar_All.pipe_right uu____9123 FStar_List.unzip))
in (match (uu____9118) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____9175 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9175) with
| (env1, uu____9185) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____9191 = (check_lbtyp top_level env lb)
in (match (uu____9191) with
| (topt, wf_annot, univ_vars, univ_opening, env1) -> begin
((match (((not (top_level)) && (univ_vars <> []))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____9214 -> begin
()
end);
(

let e1 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____9217 = (tc_maybe_toplevel_term (

let uu___121_9221 = env1
in {FStar_TypeChecker_Env.solver = uu___121_9221.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___121_9221.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___121_9221.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___121_9221.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___121_9221.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___121_9221.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___121_9221.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___121_9221.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___121_9221.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___121_9221.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___121_9221.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___121_9221.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___121_9221.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___121_9221.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___121_9221.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___121_9221.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___121_9221.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___121_9221.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___121_9221.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___121_9221.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___121_9221.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___121_9221.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___121_9221.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (uu____9217) with
| (e1, c1, g1) -> begin
(

let uu____9230 = (

let uu____9233 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____9236 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____9233 e1 c1 wf_annot))
in (match (uu____9230) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____9246 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9246) with
| true -> begin
(

let uu____9247 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____9248 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____9249 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" uu____9247 uu____9248 uu____9249))))
end
| uu____9250 -> begin
()
end));
((e1), (univ_vars), (c1), (g1), ((FStar_Option.isSome topt)));
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
| uu____9271 -> begin
()
end);
((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____9275 -> begin
(

let uu____9276 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____9276) with
| (univ_opening, univ_vars) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____9303 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (univ_opening), (uu____9303)))
end
| uu____9307 -> begin
(

let uu____9308 = (FStar_Syntax_Util.type_u ())
in (match (uu____9308) with
| (k, uu____9319) -> begin
(

let uu____9320 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____9320) with
| (t, uu____9332, g) -> begin
((

let uu____9335 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____9335) with
| true -> begin
(

let uu____9336 = (

let uu____9337 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____9337))
in (

let uu____9338 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____9336 uu____9338)))
end
| uu____9339 -> begin
()
end));
(

let t = (norm env1 t)
in (

let uu____9341 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (univ_opening), (uu____9341))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____9346 -> (match (uu____9346) with
| (x, imp) -> begin
(

let uu____9357 = (FStar_Syntax_Util.type_u ())
in (match (uu____9357) with
| (tu, u) -> begin
((

let uu____9369 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9369) with
| true -> begin
(

let uu____9370 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____9371 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____9372 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____9370 uu____9371 uu____9372))))
end
| uu____9373 -> begin
()
end));
(

let uu____9374 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____9374) with
| (t, uu____9385, g) -> begin
(

let x = (((

let uu___122_9390 = x
in {FStar_Syntax_Syntax.ppname = uu___122_9390.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___122_9390.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____9392 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____9392) with
| true -> begin
(

let uu____9393 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (

let uu____9394 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____9393 uu____9394)))
end
| uu____9395 -> begin
()
end));
(

let uu____9396 = (push_binding env x)
in ((x), (uu____9396), (g), (u)));
))
end));
)
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
(([]), (env), (FStar_TypeChecker_Rel.trivial_guard), ([]))
end
| (b)::bs -> begin
(

let uu____9447 = (tc_binder env b)
in (match (uu____9447) with
| (b, env', g, u) -> begin
(

let uu____9470 = (aux env' bs)
in (match (uu____9470) with
| (bs, env', g', us) -> begin
(

let uu____9499 = (

let uu____9500 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____9500))
in (((b)::bs), (env'), (uu____9499), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun uu____9546 uu____9547 -> (match (((uu____9546), (uu____9547))) with
| ((t, imp), (args, g)) -> begin
(

let uu____9584 = (tc_term env t)
in (match (uu____9584) with
| (t, uu____9594, g') -> begin
(

let uu____9596 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (uu____9596)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____9617 -> (match (uu____9617) with
| (pats, g) -> begin
(

let uu____9643 = (tc_args env p)
in (match (uu____9643) with
| (args, g') -> begin
(

let uu____9663 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (uu____9663)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____9683 = (tc_maybe_toplevel_term env e)
in (match (uu____9683) with
| (e, c, g) -> begin
(

let uu____9693 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____9693) with
| true -> begin
((e), (c), (g))
end
| uu____9697 -> begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let c = (norm_c env c)
in (

let uu____9703 = (

let uu____9706 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c))
in (match (uu____9706) with
| true -> begin
(

let uu____9709 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((uu____9709), (false)))
end
| uu____9710 -> begin
(

let uu____9711 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((uu____9711), (true)))
end))
in (match (uu____9703) with
| (target_comp, allow_ghost) -> begin
(

let uu____9717 = (FStar_TypeChecker_Rel.sub_comp env c target_comp)
in (match (uu____9717) with
| Some (g') -> begin
(

let uu____9723 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (uu____9723)))
end
| uu____9724 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____9729 = (

let uu____9730 = (

let uu____9733 = (FStar_TypeChecker_Err.expected_ghost_expression e c)
in ((uu____9733), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____9730))
in (Prims.raise uu____9729))
end
| uu____9737 -> begin
(

let uu____9738 = (

let uu____9739 = (

let uu____9742 = (FStar_TypeChecker_Err.expected_pure_expression e c)
in ((uu____9742), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____9739))
in (Prims.raise uu____9738))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____9755 = (tc_tot_or_gtot_term env t)
in (match (uu____9755) with
| (t, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____9775 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____9775) with
| true -> begin
(

let uu____9776 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____9776))
end
| uu____9777 -> begin
()
end));
(

let env = (

let uu___123_9779 = env
in {FStar_TypeChecker_Env.solver = uu___123_9779.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___123_9779.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___123_9779.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___123_9779.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___123_9779.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___123_9779.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___123_9779.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___123_9779.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___123_9779.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___123_9779.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___123_9779.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___123_9779.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___123_9779.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___123_9779.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___123_9779.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___123_9779.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___123_9779.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___123_9779.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___123_9779.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___123_9779.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___123_9779.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___123_9779.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___123_9779.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____9780 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Errors.Error (msg, uu____9796) -> begin
(

let uu____9797 = (

let uu____9798 = (

let uu____9801 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (uu____9801)))
in FStar_Errors.Error (uu____9798))
in (Prims.raise uu____9797))
end
in (match (uu____9780) with
| (t, c, g) -> begin
(

let uu____9811 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____9811) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____9817 -> begin
(

let uu____9818 = (

let uu____9819 = (

let uu____9822 = (

let uu____9823 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____9823))
in (

let uu____9824 = (FStar_TypeChecker_Env.get_range env)
in ((uu____9822), (uu____9824))))
in FStar_Errors.Error (uu____9819))
in (Prims.raise uu____9818))
end))
end)));
))


let level_of_type_fail = (fun env e t -> (

let uu____9845 = (

let uu____9846 = (

let uu____9849 = (

let uu____9850 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____9850 t))
in (

let uu____9851 = (FStar_TypeChecker_Env.get_range env)
in ((uu____9849), (uu____9851))))
in FStar_Errors.Error (uu____9846))
in (Prims.raise uu____9845)))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t -> (

let uu____9868 = (

let uu____9869 = (FStar_Syntax_Util.unrefine t)
in uu____9869.FStar_Syntax_Syntax.n)
in (match (uu____9868) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____9873 -> begin
(match (retry) with
| true -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (aux false t))
end
| uu____9875 -> begin
(

let uu____9876 = (FStar_Syntax_Util.type_u ())
in (match (uu____9876) with
| (t_u, u) -> begin
(

let env = (

let uu___126_9882 = env
in {FStar_TypeChecker_Env.solver = uu___126_9882.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___126_9882.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___126_9882.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___126_9882.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___126_9882.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___126_9882.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___126_9882.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___126_9882.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___126_9882.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___126_9882.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___126_9882.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___126_9882.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___126_9882.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___126_9882.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___126_9882.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___126_9882.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___126_9882.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___126_9882.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___126_9882.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___126_9882.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___126_9882.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___126_9882.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___126_9882.FStar_TypeChecker_Env.qname_and_index})
in (

let g = (FStar_TypeChecker_Rel.teq env t t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____9886 = (FStar_Syntax_Print.term_to_string t)
in (level_of_type_fail env e uu____9886))
end
| uu____9887 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____9896 = (

let uu____9897 = (FStar_Syntax_Subst.compress e)
in uu____9897.FStar_Syntax_Syntax.n)
in (match (uu____9896) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____9906) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____9917) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____9942, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____9957) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n) -> begin
n.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____9964 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9964) with
| (uu____9973, t) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____9975, FStar_Util.Inl (t), uu____9977) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____9996, FStar_Util.Inr (c), uu____9998) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u)))) None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____10028; FStar_Syntax_Syntax.pos = uu____10029; FStar_Syntax_Syntax.vars = uu____10030}, us) -> begin
(

let uu____10036 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10036) with
| (us', t) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____10052 = (

let uu____10053 = (

let uu____10056 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____10056)))
in FStar_Errors.Error (uu____10053))
in (Prims.raise uu____10052))
end
| uu____10057 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____10064 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____10065) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____10073) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____10090 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____10090) with
| (bs, c) -> begin
(

let us = (FStar_List.map (fun uu____10101 -> (match (uu____10101) with
| (b, uu____10105) -> begin
(

let uu____10106 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____10106))
end)) bs)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c)
in (

let uu____10111 = (universe_of_aux env res)
in (level_of_type env res uu____10111)))
in (

let u_c = (

let uu____10113 = (FStar_TypeChecker_Util.effect_repr env c u_res)
in (match (uu____10113) with
| None -> begin
u_res
end
| Some (trepr) -> begin
(

let uu____10116 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____10116))
end))
in (

let u = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max ((u_c)::us)))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None e.FStar_Syntax_Syntax.pos)))))
end))
end
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rec type_of_head = (fun retry hd args -> (

let hd = (FStar_Syntax_Subst.compress hd)
in (match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_type (_)) -> begin
(

let uu____10202 = (universe_of_aux env hd)
in ((uu____10202), (args)))
end
| FStar_Syntax_Syntax.Tm_match (uu____10212, (hd)::uu____10214) -> begin
(

let uu____10261 = (FStar_Syntax_Subst.open_branch hd)
in (match (uu____10261) with
| (uu____10271, uu____10272, hd) -> begin
(

let uu____10288 = (FStar_Syntax_Util.head_and_args hd)
in (match (uu____10288) with
| (hd, args) -> begin
(type_of_head retry hd args)
end))
end))
end
| uu____10323 when retry -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____10325 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____10325) with
| (hd, args) -> begin
(type_of_head false hd args)
end)))
end
| uu____10360 -> begin
(

let uu____10361 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____10361) with
| (env, uu____10375) -> begin
(

let env = (

let uu___127_10379 = env
in {FStar_TypeChecker_Env.solver = uu___127_10379.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___127_10379.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___127_10379.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___127_10379.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___127_10379.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___127_10379.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___127_10379.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___127_10379.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___127_10379.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___127_10379.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___127_10379.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___127_10379.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___127_10379.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___127_10379.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___127_10379.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___127_10379.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___127_10379.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___127_10379.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___127_10379.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___127_10379.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___127_10379.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____10381 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("UniverseOf")))
in (match (uu____10381) with
| true -> begin
(

let uu____10382 = (

let uu____10383 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____10383))
in (

let uu____10384 = (FStar_Syntax_Print.term_to_string hd)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____10382 uu____10384)))
end
| uu____10385 -> begin
()
end));
(

let uu____10386 = (tc_term env hd)
in (match (uu____10386) with
| (uu____10399, {FStar_Syntax_Syntax.eff_name = uu____10400; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____10402; FStar_Syntax_Syntax.comp = uu____10403}, g) -> begin
((

let uu____10413 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____10413 Prims.ignore));
((t), (args));
)
end));
))
end))
end)))
in (

let uu____10421 = (type_of_head true hd args)
in (match (uu____10421) with
| (t, args) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____10450 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____10450) with
| (bs, res) -> begin
(

let res = (FStar_Syntax_Util.comp_result res)
in (match (((FStar_List.length bs) = (FStar_List.length args))) with
| true -> begin
(

let subst = (FStar_Syntax_Util.subst_of_list bs args)
in (FStar_Syntax_Subst.subst subst res))
end
| uu____10482 -> begin
(

let uu____10483 = (FStar_Syntax_Print.term_to_string res)
in (level_of_type_fail env e uu____10483))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____10486, (hd)::uu____10488) -> begin
(

let uu____10535 = (FStar_Syntax_Subst.open_branch hd)
in (match (uu____10535) with
| (uu____10538, uu____10539, hd) -> begin
(universe_of_aux env hd)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____10555, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____10589 = (universe_of_aux env e)
in (level_of_type env e uu____10589)))




