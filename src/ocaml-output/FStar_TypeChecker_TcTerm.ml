
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

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e = (

let uu____1360 = (

let uu____1363 = (

let uu____1364 = (

let uu____1372 = (

let uu____1376 = (

let uu____1378 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (uu____1378)::[])
in ((false), (uu____1376)))
in ((uu____1372), (e2)))
in FStar_Syntax_Syntax.Tm_let (uu____1364))
in (FStar_Syntax_Syntax.mk uu____1363))
in (uu____1360 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____1408 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (uu____1408)))))))))
end))
end))
end
| uu____1411 -> begin
(

let uu____1412 = (tc_term env e)
in (match (uu____1412) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____1436)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let uu____1451 = (tc_term env e)
in (match (uu____1451) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), uu____1476) -> begin
(

let uu____1495 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1495) with
| (env0, uu____1503) -> begin
(

let uu____1506 = (tc_comp env0 expected_c)
in (match (uu____1506) with
| (expected_c, uu____1514, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let uu____1519 = (

let uu____1523 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____1523 e))
in (match (uu____1519) with
| (e, c', g') -> begin
(

let uu____1530 = (

let uu____1534 = (

let uu____1537 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (uu____1537)))
in (check_expected_effect env0 (Some (expected_c)) uu____1534))
in (match (uu____1530) with
| (e, expected_c, g'') -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c))))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (

let uu____1572 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____1572))
in (

let uu____1573 = (comp_check_expected_typ env e lc)
in (match (uu____1573) with
| (e, c, f2) -> begin
(

let uu____1583 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (uu____1583)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), uu____1586) -> begin
(

let uu____1605 = (FStar_Syntax_Util.type_u ())
in (match (uu____1605) with
| (k, u) -> begin
(

let uu____1613 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____1613) with
| (t, uu____1621, f) -> begin
(

let uu____1623 = (

let uu____1627 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term uu____1627 e))
in (match (uu____1623) with
| (e, c, g) -> begin
(

let uu____1634 = (

let uu____1637 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____1640 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____1637 e c f))
in (match (uu____1634) with
| (c, f) -> begin
(

let uu____1646 = (

let uu____1650 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name)))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env uu____1650 c))
in (match (uu____1646) with
| (e, c, f2) -> begin
(

let uu____1672 = (

let uu____1673 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f uu____1673))
in ((e), (c), (uu____1672)))
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

let uu____1750 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1750) with
| (unary_op, uu____1764) -> begin
(

let head = (

let uu____1782 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[]))))) None uu____1782))
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest))))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____1826; FStar_Syntax_Syntax.pos = uu____1827; FStar_Syntax_Syntax.vars = uu____1828}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____1853 -> begin
()
end);
(

let uu____1854 = (

let uu____1858 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1858) with
| (env0, uu____1866) -> begin
(tc_term env0 e)
end))
in (match (uu____1854) with
| (e, c, g) -> begin
(

let uu____1875 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1875) with
| (reify_op, uu____1889) -> begin
(

let u_c = (

let uu____1905 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (uu____1905) with
| (uu____1909, c', uu____1911) -> begin
(

let uu____1912 = (

let uu____1913 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____1913.FStar_Syntax_Syntax.n)
in (match (uu____1912) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____1917 -> begin
(

let uu____1918 = (FStar_Syntax_Util.type_u ())
in (match (uu____1918) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq env c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g')
end
| None -> begin
(

let uu____1927 = (

let uu____1928 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____1929 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____1930 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____1928 uu____1929 uu____1930))))
in (failwith uu____1927))
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

let uu____1953 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____1953 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____1954 = (comp_check_expected_typ env e c)
in (match (uu____1954) with
| (e, c, g') -> begin
(

let uu____1964 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (uu____1964)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = uu____1966; FStar_Syntax_Syntax.pos = uu____1967; FStar_Syntax_Syntax.vars = uu____1968}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____1993 -> begin
()
end);
(

let no_reflect = (fun uu____2000 -> (

let uu____2001 = (

let uu____2002 = (

let uu____2005 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((uu____2005), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____2002))
in (Prims.raise uu____2001)))
in (

let uu____2009 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2009) with
| (reflect_op, uu____2023) -> begin
(

let uu____2038 = (FStar_TypeChecker_Env.effect_decl_opt env l)
in (match (uu____2038) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
(

let uu____2044 = (

let uu____2045 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____2045)))
in (match (uu____2044) with
| true -> begin
(no_reflect ())
end
| uu____2050 -> begin
(

let uu____2051 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2051) with
| (env_no_ex, topt) -> begin
(

let uu____2062 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____2077 = (

let uu____2080 = (

let uu____2081 = (

let uu____2091 = (

let uu____2093 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____2094 = (

let uu____2096 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____2096)::[])
in (uu____2093)::uu____2094))
in ((repr), (uu____2091)))
in FStar_Syntax_Syntax.Tm_app (uu____2081))
in (FStar_Syntax_Syntax.mk uu____2080))
in (uu____2077 None top.FStar_Syntax_Syntax.pos))
in (

let uu____2106 = (

let uu____2110 = (

let uu____2111 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____2111 Prims.fst))
in (tc_tot_or_gtot_term uu____2110 t))
in (match (uu____2106) with
| (t, uu____2128, g) -> begin
(

let uu____2130 = (

let uu____2131 = (FStar_Syntax_Subst.compress t)
in uu____2131.FStar_Syntax_Syntax.n)
in (match (uu____2130) with
| FStar_Syntax_Syntax.Tm_app (uu____2142, ((res, uu____2144))::((wp, uu____2146))::[]) -> begin
((t), (res), (wp), (g))
end
| uu____2180 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____2062) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____2204 = (

let uu____2207 = (tc_tot_or_gtot_term env_no_ex e)
in (match (uu____2207) with
| (e, c, g) -> begin
((

let uu____2217 = (

let uu____2218 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____2218))
in (match (uu____2217) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____2223 -> begin
()
end));
(

let uu____2224 = (FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____2224) with
| None -> begin
((

let uu____2229 = (

let uu____2233 = (

let uu____2236 = (

let uu____2237 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2238 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____2237 uu____2238)))
in ((uu____2236), (e.FStar_Syntax_Syntax.pos)))
in (uu____2233)::[])
in (FStar_TypeChecker_Err.add_errors env uu____2229));
(

let uu____2243 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (uu____2243)));
)
end
| Some (g') -> begin
(

let uu____2245 = (

let uu____2246 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____2246))
in ((e), (uu____2245)))
end));
)
end))
in (match (uu____2204) with
| (e, g) -> begin
(

let c = (

let uu____2253 = (

let uu____2254 = (

let uu____2255 = (

let uu____2256 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (uu____2256)::[])
in (

let uu____2257 = (

let uu____2263 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2263)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____2255; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____2257; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____2254))
in (FStar_All.pipe_right uu____2253 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[]))))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____2284 = (comp_check_expected_typ env e c)
in (match (uu____2284) with
| (e, c, g') -> begin
(

let uu____2294 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (uu____2294)))
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

let uu____2313 = (

let uu____2314 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____2314 Prims.fst))
in (FStar_All.pipe_right uu____2313 instantiate_both))
in ((

let uu____2323 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____2323) with
| true -> begin
(

let uu____2324 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____2325 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____2324 uu____2325)))
end
| uu____2326 -> begin
()
end));
(

let uu____2327 = (tc_term (no_inst env) head)
in (match (uu____2327) with
| (head, chead, g_head) -> begin
(

let uu____2337 = (

let uu____2341 = ((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head))
in (match (uu____2341) with
| true -> begin
(

let uu____2345 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args uu____2345))
end
| uu____2347 -> begin
(

let uu____2348 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args uu____2348))
end))
in (match (uu____2337) with
| (e, c, g) -> begin
((

let uu____2357 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2357) with
| true -> begin
(

let uu____2358 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____2358))
end
| uu____2359 -> begin
()
end));
(

let c = (

let uu____2361 = (((FStar_TypeChecker_Env.should_verify env) && (

let uu____2362 = (FStar_Syntax_Util.is_lcomp_partial_return c)
in (not (uu____2362)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____2361) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end
| uu____2363 -> begin
c
end))
in (

let uu____2364 = (comp_check_expected_typ env0 e c)
in (match (uu____2364) with
| (e, c, g') -> begin
(

let gimp = (

let uu____2375 = (

let uu____2376 = (FStar_Syntax_Subst.compress head)
in uu____2376.FStar_Syntax_Syntax.n)
in (match (uu____2375) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____2380) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let uu___90_2412 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___90_2412.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___90_2412.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___90_2412.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____2437 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (

let uu____2439 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g uu____2439))
in ((

let uu____2441 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2441) with
| true -> begin
(

let uu____2442 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____2443 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____2442 uu____2443)))
end
| uu____2444 -> begin
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

let uu____2473 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2473) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let uu____2485 = (tc_term env1 e1)
in (match (uu____2485) with
| (e1, c1, g1) -> begin
(

let uu____2495 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let uu____2501 = (FStar_Syntax_Util.type_u ())
in (match (uu____2501) with
| (k, uu____2507) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (

let uu____2509 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((uu____2509), (res_t))))
end))
end)
in (match (uu____2495) with
| (env_branches, res_t) -> begin
((

let uu____2516 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2516) with
| true -> begin
(

let uu____2517 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____2517))
end
| uu____2518 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____2568 = (

let uu____2571 = (FStar_List.fold_right (fun uu____2590 uu____2591 -> (match (((uu____2590), (uu____2591))) with
| ((uu____2623, f, c, g), (caccum, gaccum)) -> begin
(

let uu____2656 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (uu____2656)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____2571) with
| (cases, g) -> begin
(

let uu____2677 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((uu____2677), (g)))
end))
in (match (uu____2568) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____2730 -> (match (uu____2730) with
| ((pat, wopt, br), uu____2746, lc, uu____2748) -> begin
(

let uu____2755 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (uu____2755)))
end))))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name)))))) None e.FStar_Syntax_Syntax.pos)))))
in (

let uu____2795 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____2795) with
| true -> begin
(mk_match e1)
end
| uu____2798 -> begin
(

let e_match = (

let uu____2802 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____2802))
in (

let lb = (

let uu____2806 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = uu____2806; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = (

let uu____2810 = (

let uu____2813 = (

let uu____2814 = (

let uu____2822 = (

let uu____2823 = (

let uu____2824 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____2824)::[])
in (FStar_Syntax_Subst.close uu____2823 e_match))
in ((((false), ((lb)::[]))), (uu____2822)))
in FStar_Syntax_Syntax.Tm_let (uu____2814))
in (FStar_Syntax_Syntax.mk uu____2813))
in (uu____2810 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____2838 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2838) with
| true -> begin
(

let uu____2839 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____2840 = (

let uu____2841 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2841))
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____2839 uu____2840)))
end
| uu____2842 -> begin
()
end));
(

let uu____2843 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (uu____2843)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2846); FStar_Syntax_Syntax.lbunivs = uu____2847; FStar_Syntax_Syntax.lbtyp = uu____2848; FStar_Syntax_Syntax.lbeff = uu____2849; FStar_Syntax_Syntax.lbdef = uu____2850})::[]), uu____2851) -> begin
((

let uu____2866 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2866) with
| true -> begin
(

let uu____2867 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____2867))
end
| uu____2868 -> begin
()
end));
(check_top_level_let env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____2869), uu____2870) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2880); FStar_Syntax_Syntax.lbunivs = uu____2881; FStar_Syntax_Syntax.lbtyp = uu____2882; FStar_Syntax_Syntax.lbeff = uu____2883; FStar_Syntax_Syntax.lbdef = uu____2884})::uu____2885), uu____2886) -> begin
((

let uu____2902 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2902) with
| true -> begin
(

let uu____2903 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____2903))
end
| uu____2904 -> begin
()
end));
(check_top_level_let_rec env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____2905), uu____2906) -> begin
(check_inner_let_rec env top)
end));
)))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let uu____2950 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____2950) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____2963 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2963) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____2966 -> begin
(

let uu____2967 = (

let uu____2968 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____2968))
in FStar_Util.Inr (uu____2967))
end))
in (

let is_data_ctor = (fun uu___78_2977 -> (match (uu___78_2977) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| uu____2980 -> begin
false
end))
in (

let uu____2982 = ((is_data_ctor dc) && (

let uu____2983 = (FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)
in (not (uu____2983))))
in (match (uu____2982) with
| true -> begin
(

let uu____2989 = (

let uu____2990 = (

let uu____2993 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____2996 = (FStar_TypeChecker_Env.get_range env)
in ((uu____2993), (uu____2996))))
in FStar_Errors.Error (uu____2990))
in (Prims.raise uu____2989))
end
| uu____3000 -> begin
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

let uu____3007 = (

let uu____3008 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____3008))
in (failwith uu____3007))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____3027 = (

let uu____3028 = (FStar_Syntax_Subst.compress t1)
in uu____3028.FStar_Syntax_Syntax.n)
in (match (uu____3027) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3031) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____3039 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___91_3059 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___91_3059.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___91_3059.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___91_3059.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3087 = (

let uu____3094 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____3094) with
| None -> begin
(

let uu____3102 = (FStar_Syntax_Util.type_u ())
in (match (uu____3102) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____3087) with
| (t, uu____3123, g0) -> begin
(

let uu____3131 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (uu____3131) with
| (e, uu____3142, g1) -> begin
(

let uu____3150 = (

let uu____3151 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____3151 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____3152 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (uu____3150), (uu____3152))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (match (env.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____3159 -> begin
(FStar_TypeChecker_Env.lookup_bv env x)
end)
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let uu___92_3161 = x
in {FStar_Syntax_Syntax.ppname = uu___92_3161.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___92_3161.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let uu____3162 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____3162) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____3175 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____3175) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____3178 -> begin
(

let uu____3179 = (

let uu____3180 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3180))
in FStar_Util.Inr (uu____3179))
end))
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____3186; FStar_Syntax_Syntax.pos = uu____3187; FStar_Syntax_Syntax.vars = uu____3188}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let uu____3196 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3196) with
| (us', t) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____3213 = (

let uu____3214 = (

let uu____3217 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____3217)))
in FStar_Errors.Error (uu____3214))
in (Prims.raise uu____3213))
end
| uu____3218 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____3225 -> begin
(failwith "Impossible")
end)) us' us)
end);
(

let fv' = (

let uu___93_3227 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___94_3228 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___94_3228.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___94_3228.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___93_3227.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___93_3227.FStar_Syntax_Syntax.fv_qual})
in (

let e = (

let uu____3242 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3242 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3254 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3254) with
| (us, t) -> begin
((

let uu____3267 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Range")))
in (match (uu____3267) with
| true -> begin
(

let uu____3268 = (

let uu____3269 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____3269))
in (

let uu____3270 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____3271 = (

let uu____3272 = (

let uu____3273 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid uu____3273))
in (FStar_Range.string_of_range uu____3272))
in (

let uu____3274 = (

let uu____3275 = (

let uu____3276 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid uu____3276))
in (FStar_Range.string_of_use_range uu____3275))
in (

let uu____3277 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s" uu____3268 uu____3270 uu____3271 uu____3274 uu____3277))))))
end
| uu____3278 -> begin
()
end));
(

let fv' = (

let uu___95_3280 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___96_3281 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___96_3281.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___96_3281.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___95_3280.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___95_3280.FStar_Syntax_Syntax.fv_qual})
in (

let e = (

let uu____3295 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3295 us))
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

let uu____3331 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3331) with
| (bs, c) -> begin
(

let env0 = env
in (

let uu____3340 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3340) with
| (env, uu____3348) -> begin
(

let uu____3351 = (tc_binders env bs)
in (match (uu____3351) with
| (bs, env, g, us) -> begin
(

let uu____3363 = (tc_comp env c)
in (match (uu____3363) with
| (c, uc, f) -> begin
(

let e = (

let uu___97_3376 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = uu___97_3376.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___97_3376.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___97_3376.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env e bs c);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____3397 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g uu____3397))
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

let uu____3432 = (

let uu____3435 = (

let uu____3436 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3436)::[])
in (FStar_Syntax_Subst.open_term uu____3435 phi))
in (match (uu____3432) with
| (x, phi) -> begin
(

let env0 = env
in (

let uu____3443 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3443) with
| (env, uu____3451) -> begin
(

let uu____3454 = (

let uu____3461 = (FStar_List.hd x)
in (tc_binder env uu____3461))
in (match (uu____3454) with
| (x, env, f1, u) -> begin
((

let uu____3478 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____3478) with
| true -> begin
(

let uu____3479 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3480 = (FStar_Syntax_Print.term_to_string phi)
in (

let uu____3481 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____3479 uu____3480 uu____3481))))
end
| uu____3482 -> begin
()
end));
(

let uu____3483 = (FStar_Syntax_Util.type_u ())
in (match (uu____3483) with
| (t_phi, uu____3490) -> begin
(

let uu____3491 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (uu____3491) with
| (phi, uu____3499, f2) -> begin
(

let e = (

let uu___98_3504 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = uu___98_3504.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___98_3504.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___98_3504.FStar_Syntax_Syntax.vars})
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____3523 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____3523))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____3532) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in ((

let uu____3557 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3557) with
| true -> begin
(

let uu____3558 = (FStar_Syntax_Print.term_to_string (

let uu___99_3559 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = uu___99_3559.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___99_3559.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___99_3559.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____3558))
end
| uu____3577 -> begin
()
end));
(

let uu____3578 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3578) with
| (bs, body) -> begin
(tc_abs env top bs body)
end));
))
end
| uu____3586 -> begin
(

let uu____3587 = (

let uu____3588 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____3589 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____3588 uu____3589)))
in (failwith uu____3587))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (uu____3595) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (uu____3596, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (uu____3602, Some (uu____3603)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____3611) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (uu____3615) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (uu____3616) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____3617) -> begin
FStar_TypeChecker_Common.t_range
end
| uu____3618 -> begin
(Prims.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____3629) -> begin
(

let uu____3636 = (FStar_Syntax_Util.type_u ())
in (match (uu____3636) with
| (k, u) -> begin
(

let uu____3644 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3644) with
| (t, uu____3652, g) -> begin
(

let uu____3654 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((uu____3654), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____3656) -> begin
(

let uu____3663 = (FStar_Syntax_Util.type_u ())
in (match (uu____3663) with
| (k, u) -> begin
(

let uu____3671 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3671) with
| (t, uu____3679, g) -> begin
(

let uu____3681 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((uu____3681), (u), (g)))
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

let uu____3697 = (

let uu____3698 = (

let uu____3699 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____3699)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head uu____3698))
in (uu____3697 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____3704 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____3704) with
| (tc, uu____3712, f) -> begin
(

let uu____3714 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3714) with
| (head, args) -> begin
(

let comp_univs = (

let uu____3744 = (

let uu____3745 = (FStar_Syntax_Subst.compress head)
in uu____3745.FStar_Syntax_Syntax.n)
in (match (uu____3744) with
| FStar_Syntax_Syntax.Tm_uinst (uu____3748, us) -> begin
us
end
| uu____3754 -> begin
[]
end))
in (

let uu____3755 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3755) with
| (uu____3768, args) -> begin
(

let uu____3784 = (

let uu____3796 = (FStar_List.hd args)
in (

let uu____3805 = (FStar_List.tl args)
in ((uu____3796), (uu____3805))))
in (match (uu____3784) with
| (res, args) -> begin
(

let uu____3847 = (

let uu____3852 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___79_3862 -> (match (uu___79_3862) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____3868 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3868) with
| (env, uu____3875) -> begin
(

let uu____3878 = (tc_tot_or_gtot_term env e)
in (match (uu____3878) with
| (e, uu____3885, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____3852 FStar_List.unzip))
in (match (uu____3847) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let uu___100_3908 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___100_3908.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = uu___100_3908.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____3912 = (FStar_TypeChecker_Util.effect_repr env c u)
in (match (uu____3912) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____3915 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (uu____3915))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____3923) -> begin
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

let uu____3926 = (aux u)
in FStar_Syntax_Syntax.U_succ (uu____3926))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____3929 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____3929))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____3932 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____3933 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____3933 Prims.snd))
end
| uu____3938 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (

let uu____3959 = (

let uu____3960 = (

let uu____3963 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((uu____3963), (top.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____3960))
in (Prims.raise uu____3959)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun uu____4021 bs bs_expected -> (match (uu____4021) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
((match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(

let uu____4118 = (

let uu____4119 = (

let uu____4122 = (

let uu____4123 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____4123))
in (

let uu____4124 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((uu____4122), (uu____4124))))
in FStar_Errors.Error (uu____4119))
in (Prims.raise uu____4118))
end
| uu____4125 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____4129 = (

let uu____4132 = (

let uu____4133 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in uu____4133.FStar_Syntax_Syntax.n)
in (match (uu____4132) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____4138 -> begin
((

let uu____4140 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____4140) with
| true -> begin
(

let uu____4141 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" uu____4141))
end
| uu____4142 -> begin
()
end));
(

let uu____4143 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (uu____4143) with
| (t, uu____4150, g1) -> begin
(

let g2 = (

let uu____4153 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4154 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard uu____4153 "Type annotation on parameter incompatible with the expected type" uu____4154)))
in (

let g = (

let uu____4156 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____4156))
in ((t), (g))))
end));
)
end))
in (match (uu____4129) with
| (t, g) -> begin
(

let hd = (

let uu___101_4172 = hd
in {FStar_Syntax_Syntax.ppname = uu___101_4172.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___101_4172.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (

let uu____4181 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected uu____4181))
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
| uu____4277 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____4281 = (tc_binders env bs)
in (match (uu____4281) with
| (bs, envbody, g, uu____4300) -> begin
(

let uu____4301 = (

let uu____4306 = (

let uu____4307 = (FStar_Syntax_Subst.compress body)
in uu____4307.FStar_Syntax_Syntax.n)
in (match (uu____4306) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), uu____4316) -> begin
(

let uu____4335 = (tc_comp envbody c)
in (match (uu____4335) with
| (c, uu____4344, g') -> begin
(

let uu____4346 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (uu____4346)))
end))
end
| uu____4348 -> begin
((None), (body), (g))
end))
in (match (uu____4301) with
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

let uu____4398 = (

let uu____4399 = (FStar_Syntax_Subst.compress t)
in uu____4399.FStar_Syntax_Syntax.n)
in (match (uu____4398) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
((match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4430 -> begin
(failwith "Impossible")
end);
(

let uu____4434 = (tc_binders env bs)
in (match (uu____4434) with
| (bs, envbody, g, uu____4454) -> begin
(

let uu____4455 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____4455) with
| (envbody, uu____4472) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____4483) -> begin
(

let uu____4488 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (uu____4488) with
| (uu____4513, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____4549 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____4549) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun uu____4610 c_expected -> (match (uu____4610) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(

let uu____4671 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (uu____4671)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____4688 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total uu____4688))
in (

let uu____4689 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (uu____4689))))
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

let uu____4730 = (check_binders env more_bs bs_expected)
in (match (uu____4730) with
| (env, bs', more, guard', subst) -> begin
(

let uu____4769 = (

let uu____4785 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (uu____4785), (subst)))
in (handle_more uu____4769 c_expected))
end))
end
| uu____4795 -> begin
(

let uu____4796 = (

let uu____4797 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" uu____4797))
in (fail uu____4796 t))
end))
end
| uu____4805 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end))
end)
end))
in (

let uu____4813 = (check_binders env bs bs_expected)
in (handle_more uu____4813 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let uu___102_4851 = envbody
in {FStar_TypeChecker_Env.solver = uu___102_4851.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___102_4851.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___102_4851.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___102_4851.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___102_4851.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___102_4851.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___102_4851.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___102_4851.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___102_4851.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___102_4851.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___102_4851.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___102_4851.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___102_4851.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___102_4851.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___102_4851.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___102_4851.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___102_4851.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___102_4851.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___102_4851.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___102_4851.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___102_4851.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___102_4851.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___102_4851.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____4865 uu____4866 -> (match (((uu____4865), (uu____4866))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let uu____4891 = (

let uu____4895 = (

let uu____4896 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____4896 Prims.fst))
in (tc_term uu____4895 t))
in (match (uu____4891) with
| (t, uu____4908, uu____4909) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____4916 = (FStar_Syntax_Syntax.mk_binder (

let uu___103_4917 = x
in {FStar_Syntax_Syntax.ppname = uu___103_4917.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___103_4917.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____4916)::letrec_binders)
end
| uu____4918 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let uu____4921 = (check_actuals_against_formals env bs bs_expected)
in (match (uu____4921) with
| (envbody, bs, g, c) -> begin
(

let uu____4951 = (

let uu____4955 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____4955) with
| true -> begin
(mk_letrec_env envbody bs c)
end
| uu____4959 -> begin
((envbody), ([]))
end))
in (match (uu____4951) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| uu____4988 -> begin
(match ((not (norm))) with
| true -> begin
(

let uu____5001 = (unfold_whnf env t)
in (as_function_typ true uu____5001))
end
| uu____5002 -> begin
(

let uu____5003 = (expected_function_typ env None body)
in (match (uu____5003) with
| (uu____5027, bs, uu____5029, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end)
end)))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____5050 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____5050) with
| (env, topt) -> begin
((

let uu____5062 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5062) with
| true -> begin
(

let uu____5063 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____5063 (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____5065 -> begin
"false"
end)))
end
| uu____5066 -> begin
()
end));
(

let uu____5067 = (expected_function_typ env topt body)
in (match (uu____5067) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let uu____5097 = (tc_term (

let uu___104_5101 = envbody
in {FStar_TypeChecker_Env.solver = uu___104_5101.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___104_5101.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___104_5101.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___104_5101.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___104_5101.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___104_5101.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___104_5101.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___104_5101.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___104_5101.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___104_5101.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___104_5101.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___104_5101.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___104_5101.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___104_5101.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___104_5101.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___104_5101.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___104_5101.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___104_5101.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___104_5101.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___104_5101.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___104_5101.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___104_5101.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (uu____5097) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in ((

let uu____5110 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))
in (match (uu____5110) with
| true -> begin
(

let uu____5111 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (

let uu____5120 = (

let uu____5121 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____5121))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" uu____5111 uu____5120)))
end
| uu____5122 -> begin
()
end));
(

let uu____5123 = (

let uu____5127 = (

let uu____5130 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (uu____5130)))
in (check_expected_effect (

let uu___105_5135 = envbody
in {FStar_TypeChecker_Env.solver = uu___105_5135.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___105_5135.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___105_5135.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___105_5135.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___105_5135.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___105_5135.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___105_5135.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___105_5135.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___105_5135.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___105_5135.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___105_5135.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___105_5135.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___105_5135.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___105_5135.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___105_5135.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___105_5135.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___105_5135.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___105_5135.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___105_5135.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___105_5135.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___105_5135.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___105_5135.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___105_5135.FStar_TypeChecker_Env.qname_and_index}) c_opt uu____5127))
in (match (uu____5123) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = (

let uu____5144 = (env.FStar_TypeChecker_Env.top_level || (

let uu____5145 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____5145))))
in (match (uu____5144) with
| true -> begin
(

let uu____5146 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____5146))
end
| uu____5147 -> begin
(

let guard = (

let uu____5149 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) uu____5149))
in guard)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (

let uu____5156 = (

let uu____5163 = (

let uu____5169 = (FStar_All.pipe_right (FStar_Util.dflt cbody c_opt) FStar_Syntax_Util.lcomp_of_comp)
in (FStar_All.pipe_right uu____5169 (fun _0_29 -> FStar_Util.Inl (_0_29))))
in Some (uu____5163))
in (FStar_Syntax_Util.abs bs body uu____5156))
in (

let uu____5183 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5198) -> begin
((e), (t), (guard))
end
| uu____5206 -> begin
(

let uu____5207 = (match (use_teq) with
| true -> begin
(

let uu____5212 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (uu____5212)))
end
| uu____5213 -> begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end)
in (match (uu____5207) with
| (e, guard') -> begin
(

let uu____5219 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (uu____5219)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (uu____5183) with
| (e, tfun, guard) -> begin
(

let c = (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____5231 -> begin
(FStar_TypeChecker_Util.return_value env tfun e)
end)
in (

let uu____5232 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (uu____5232) with
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

let uu____5268 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5268) with
| true -> begin
(

let uu____5269 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (

let uu____5270 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____5269 uu____5270)))
end
| uu____5271 -> begin
()
end));
(

let monadic_application = (fun uu____5312 subst arg_comps_rev arg_rets guard fvs bs -> (match (uu____5312) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___106_5353 = cres
in {FStar_Syntax_Syntax.eff_name = uu___106_5353.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___106_5353.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___106_5353.FStar_Syntax_Syntax.comp})
in (

let uu____5354 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun uu___80_5381 -> (match (uu___80_5381) with
| (uu____5390, uu____5391, FStar_Util.Inl (uu____5392)) -> begin
false
end
| (uu____5403, uu____5404, FStar_Util.Inr (c)) -> begin
(

let uu____5414 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (not (uu____5414)))
end)))))
in (

let cres = (match (refine_with_equality) with
| true -> begin
(

let uu____5416 = ((FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets)) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env uu____5416 cres))
end
| uu____5425 -> begin
((

let uu____5427 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5427) with
| true -> begin
(

let uu____5428 = (FStar_Syntax_Print.term_to_string head)
in (

let uu____5429 = (FStar_Syntax_Print.lcomp_to_string cres)
in (

let uu____5430 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" uu____5428 uu____5429 uu____5430))))
end
| uu____5431 -> begin
()
end));
cres;
)
end)
in ((cres), (g))))))
end
| uu____5432 -> begin
(

let g = (

let uu____5437 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right uu____5437 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (

let uu____5438 = (

let uu____5439 = (

let uu____5442 = (

let uu____5443 = (

let uu____5444 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs uu____5444))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) uu____5443))
in (FStar_Syntax_Syntax.mk_Total uu____5442))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5439))
in ((uu____5438), (g))))
end)
in (match (uu____5354) with
| (cres, guard) -> begin
((

let uu____5455 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5455) with
| true -> begin
(

let uu____5456 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____5456))
end
| uu____5457 -> begin
()
end));
(

let comp = (FStar_List.fold_left (fun out_c uu____5472 -> (match (uu____5472) with
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

let uu____5518 = (

let uu____5519 = (FStar_Syntax_Subst.compress head)
in uu____5519.FStar_Syntax_Syntax.n)
in (match (uu____5518) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Or))
end
| uu____5523 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args = (FStar_List.fold_left (fun args uu____5537 -> (match (uu____5537) with
| (arg, uu____5549, uu____5550) -> begin
(arg)::args
end)) [] arg_comps_rev)
in (

let app = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_lift env app cres.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ))))
end
| uu____5569 -> begin
(

let uu____5570 = (

let map_fun = (fun uu____5609 -> (match (uu____5609) with
| ((e, q), uu____5633, c0) -> begin
(match (c0) with
| FStar_Util.Inl (uu____5658) -> begin
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

let uu____5701 = (

let uu____5704 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____5704), (q)))
in ((Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e)))), (uu____5701)))))
end)
end))
in (

let uu____5722 = (

let uu____5736 = (

let uu____5749 = (

let uu____5761 = (

let uu____5770 = (FStar_Syntax_Syntax.as_arg head)
in ((uu____5770), (None), (FStar_Util.Inr (chead))))
in (uu____5761)::arg_comps_rev)
in (FStar_List.map map_fun uu____5749))
in (FStar_All.pipe_left FStar_List.split uu____5736))
in (match (uu____5722) with
| (lifted_args, reverse_args) -> begin
(

let uu____5879 = (

let uu____5880 = (FStar_List.hd reverse_args)
in (Prims.fst uu____5880))
in (

let uu____5885 = (

let uu____5889 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____5889))
in ((lifted_args), (uu____5879), (uu____5885))))
end)))
in (match (uu____5570) with
| (lifted_args, head, args) -> begin
(

let app = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_lift env app cres.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
in (

let app = (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___81_5957 -> (match (uu___81_5957) with
| None -> begin
e
end
| Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1)
in (

let letbinding = (

let uu____5999 = (

let uu____6002 = (

let uu____6003 = (

let uu____6011 = (

let uu____6012 = (

let uu____6013 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6013)::[])
in (FStar_Syntax_Subst.close uu____6012 e))
in ((((false), ((lb)::[]))), (uu____6011)))
in FStar_Syntax_Syntax.Tm_let (uu____6003))
in (FStar_Syntax_Syntax.mk uu____6002))
in (uu____5999 None e.FStar_Syntax_Syntax.pos))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp.FStar_Syntax_Syntax.res_typ)))))))) None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app lifted_args)))))
end))
end)
in (

let uu____6047 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (uu____6047) with
| (comp, g) -> begin
((app), (comp), (g))
end))))));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____6105 bs args -> (match (uu____6105) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (uu____6200))))::rest, ((uu____6202, None))::uu____6203) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let uu____6240 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (uu____6240) with
| (varg, uu____6251, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (

let uu____6264 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____6264)))
in (

let uu____6265 = (

let uu____6287 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (FStar_Util.Inl (((FStar_Syntax_Const.effect_Tot_lid), (t))))))::outargs), ((arg)::arg_rets), (uu____6287), (fvs)))
in (tc_args head_info uu____6265 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| uu____6378 -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___107_6385 = x
in {FStar_Syntax_Syntax.ppname = uu___107_6385.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_6385.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____6387 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____6387) with
| true -> begin
(

let uu____6388 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____6388))
end
| uu____6389 -> begin
()
end));
(

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let uu___108_6393 = env
in {FStar_TypeChecker_Env.solver = uu___108_6393.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___108_6393.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___108_6393.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___108_6393.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___108_6393.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___108_6393.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___108_6393.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___108_6393.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___108_6393.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___108_6393.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___108_6393.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___108_6393.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___108_6393.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___108_6393.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___108_6393.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___108_6393.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___108_6393.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___108_6393.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___108_6393.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___108_6393.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___108_6393.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___108_6393.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___108_6393.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____6395 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6395) with
| true -> begin
(

let uu____6396 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____6397 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6398 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____6396 uu____6397 uu____6398))))
end
| uu____6399 -> begin
()
end));
(

let uu____6400 = (tc_term env e)
in (match (uu____6400) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in (

let uu____6416 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____6416) with
| true -> begin
(

let subst = (

let uu____6421 = (FStar_List.hd bs)
in (maybe_extend_subst subst uu____6421 e))
in (tc_args head_info ((subst), ((((arg), (None), (FStar_Util.Inl (((c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ))))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____6476 -> begin
(

let uu____6477 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name)
in (match (uu____6477) with
| true -> begin
(

let subst = (

let uu____6482 = (FStar_List.hd bs)
in (maybe_extend_subst subst uu____6482 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____6527 -> begin
(

let uu____6528 = (

let uu____6529 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder uu____6529))
in (match (uu____6528) with
| true -> begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (

let uu____6538 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6538))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end
| uu____6575 -> begin
(

let uu____6576 = (

let uu____6598 = (

let uu____6600 = (

let uu____6601 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____6601))
in (uu____6600)::arg_rets)
in ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), (uu____6598), (g), ((x)::fvs)))
in (tc_args head_info uu____6576 rest rest'))
end))
end))
end))))
end));
))));
)));
)
end
| (uu____6638, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____6659) -> begin
(

let uu____6689 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (uu____6689) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (

let uu____6712 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____6712 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let uu____6728 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (uu____6728) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in ((

let uu____6742 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6742) with
| true -> begin
(

let uu____6743 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" uu____6743))
end
| uu____6744 -> begin
()
end));
(tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args);
))
end))
end
| uu____6773 when (not (norm)) -> begin
(

let uu____6774 = (unfold_whnf env tres)
in (aux true uu____6774))
end
| uu____6775 -> begin
(

let uu____6776 = (

let uu____6777 = (

let uu____6780 = (

let uu____6781 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____6782 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" uu____6781 uu____6782)))
in (

let uu____6786 = (FStar_Syntax_Syntax.argpos arg)
in ((uu____6780), (uu____6786))))
in FStar_Errors.Error (uu____6777))
in (Prims.raise uu____6776))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (

let uu____6802 = (

let uu____6803 = (FStar_Syntax_Util.unrefine tf)
in uu____6803.FStar_Syntax_Syntax.n)
in (match (uu____6802) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let uu____6879 = (tc_term env e)
in (match (uu____6879) with
| (e, c, g_e) -> begin
(

let uu____6892 = (tc_args env tl)
in (match (uu____6892) with
| (args, comps, g_rest) -> begin
(

let uu____6914 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____6914)))
end))
end))
end))
in (

let uu____6925 = (tc_args env args)
in (match (uu____6925) with
| (args, comps, g_args) -> begin
(

let bs = (

let uu____6950 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____6970 -> (match (uu____6970) with
| (uu____6978, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____6950))
in (

let ml_or_tot = (

let uu____6988 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)
in (match (uu____6988) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| uu____6996 -> begin
FStar_Syntax_Util.ml_comp
end))
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(

let uu____7008 = (

let uu____7009 = (FStar_Syntax_Subst.compress t)
in uu____7009.FStar_Syntax_Syntax.n)
in (match (uu____7008) with
| FStar_Syntax_Syntax.Tm_type (uu____7016) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| uu____7019 -> begin
ml_or_tot
end))
end)
in (

let cres = (

let uu____7021 = (

let uu____7022 = (

let uu____7023 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7023 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____7022))
in (ml_or_tot uu____7021 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____7032 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____7032) with
| true -> begin
(

let uu____7033 = (FStar_Syntax_Print.term_to_string head)
in (

let uu____7034 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____7035 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____7033 uu____7034 uu____7035))))
end
| uu____7036 -> begin
()
end));
(

let uu____7038 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____7038));
(

let comp = (

let uu____7040 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____7045 out -> (match (uu____7045) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____7040))
in (

let uu____7054 = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let uu____7061 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____7054), (comp), (uu____7061)))));
))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7076 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7076) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| uu____7119 -> begin
(match ((not (norm))) with
| true -> begin
(

let uu____7125 = (unfold_whnf env tf)
in (check_function_app true uu____7125))
end
| uu____7126 -> begin
(

let uu____7127 = (

let uu____7128 = (

let uu____7131 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((uu____7131), (head.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____7128))
in (Prims.raise uu____7127))
end)
end)))
in (

let uu____7137 = (

let uu____7138 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____7138))
in (check_function_app false uu____7137)))));
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

let uu____7184 = (FStar_List.fold_left2 (fun uu____7197 uu____7198 uu____7199 -> (match (((uu____7197), (uu____7198), (uu____7199))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((aq <> aq')) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7242 -> begin
()
end);
(

let uu____7243 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____7243) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (

let uu____7255 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____7255 g))
in (

let ghost = (ghost || ((

let uu____7257 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____7257))) && (

let uu____7258 = (FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)
in (not (uu____7258)))))
in (

let uu____7259 = (

let uu____7265 = (

let uu____7271 = (FStar_Syntax_Syntax.as_arg e)
in (uu____7271)::[])
in (FStar_List.append seen uu____7265))
in (

let uu____7276 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((uu____7259), (uu____7276), (ghost)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____7184) with
| (args, guard, ghost) -> begin
(

let e = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = (match (ghost) with
| true -> begin
(

let uu____7305 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____7305 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____7306 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____7307 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (uu____7307) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| uu____7319 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let uu____7341 = (FStar_Syntax_Subst.open_branch branch)
in (match (uu____7341) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____7367 = branch
in (match (uu____7367) with
| (cpat, uu____7387, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let uu____7429 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (uu____7429) with
| (pat_bvs, exps, p) -> begin
((

let uu____7451 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7451) with
| true -> begin
(

let uu____7452 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____7453 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____7452 uu____7453)))
end
| uu____7454 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let uu____7456 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____7456) with
| (env1, uu____7469) -> begin
(

let env1 = (

let uu___109_7473 = env1
in {FStar_TypeChecker_Env.solver = uu___109_7473.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___109_7473.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___109_7473.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___109_7473.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___109_7473.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___109_7473.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___109_7473.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___109_7473.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___109_7473.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___109_7473.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___109_7473.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___109_7473.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___109_7473.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___109_7473.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___109_7473.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___109_7473.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___109_7473.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___109_7473.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___109_7473.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___109_7473.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___109_7473.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___109_7473.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___109_7473.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let uu____7475 = (

let uu____7480 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> ((

let uu____7492 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7492) with
| true -> begin
(

let uu____7493 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7494 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____7493 uu____7494)))
end
| uu____7495 -> begin
()
end));
(

let uu____7496 = (tc_term env1 e)
in (match (uu____7496) with
| (e, lc, g) -> begin
((

let uu____7506 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7506) with
| true -> begin
(

let uu____7507 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____7508 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" uu____7507 uu____7508)))
end
| uu____7509 -> begin
()
end));
(

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let uu____7512 = (

let uu____7513 = (FStar_TypeChecker_Rel.discharge_guard env (

let uu___110_7514 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___110_7514.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___110_7514.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___110_7514.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right uu____7513 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (

let uu____7528 = (

let uu____7530 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right uu____7530 (FStar_List.map (fun uu____7554 -> (match (uu____7554) with
| (u, uu____7559) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right uu____7528 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____7572 = (

let uu____7573 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____7573))
in (match (uu____7572) with
| true -> begin
(

let unresolved = (

let uu____7580 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right uu____7580 FStar_Util.set_elements))
in (

let uu____7594 = (

let uu____7595 = (

let uu____7598 = (

let uu____7599 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (

let uu____7600 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____7601 = (

let uu____7602 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____7614 -> (match (uu____7614) with
| (u, uu____7622) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____7602 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____7599 uu____7600 uu____7601))))
in ((uu____7598), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____7595))
in (Prims.raise uu____7594)))
end
| uu____7635 -> begin
()
end));
(

let uu____7637 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7637) with
| true -> begin
(

let uu____7638 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____7638))
end
| uu____7639 -> begin
()
end));
((e), (e'));
))))))));
)
end));
))))
in (FStar_All.pipe_right uu____7480 FStar_List.unzip))
in (match (uu____7475) with
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

let uu____7669 = (

let uu____7673 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____7673 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____7669) with
| (scrutinee_env, uu____7686) -> begin
(

let uu____7689 = (tc_pat true pat_t pattern)
in (match (uu____7689) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let uu____7717 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
(

let uu____7732 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____7732) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7739 -> begin
(

let uu____7740 = (

let uu____7744 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term uu____7744 e))
in (match (uu____7740) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end))
end)
in (match (uu____7717) with
| (when_clause, g_when) -> begin
(

let uu____7764 = (tc_term pat_env branch_exp)
in (match (uu____7764) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____7789 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____7789))
end)
in (

let uu____7799 = (

let eqs = (

let uu____7807 = (

let uu____7808 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7808)))
in (match (uu____7807) with
| true -> begin
None
end
| uu____7814 -> begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| uu____7834 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(

let uu____7854 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____7854))
end))
end))) None))
end))
in (

let uu____7866 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (uu____7866) with
| (c, g_branch) -> begin
(

let uu____7876 = (match (((eqs), (when_condition))) with
| uu____7887 when (

let uu____7896 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7896))) -> begin
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

let uu____7922 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (

let uu____7923 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____7922), (uu____7923))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____7942 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____7942))
in (

let uu____7943 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (

let uu____7944 = (

let uu____7945 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____7945 g_when))
in ((uu____7943), (uu____7944))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____7961 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((uu____7961), (g_when)))))
end)
in (match (uu____7876) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (

let uu____7969 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (

let uu____7970 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((uu____7969), (uu____7970), (g_branch)))))
end))
end)))
in (match (uu____7799) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let uu____7983 = (

let uu____7984 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7984)))
in (match (uu____7983) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____7985 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> (

let uu____8017 = (

let uu____8018 = (

let uu____8019 = (

let uu____8021 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____8021))
in (FStar_List.length uu____8019))
in (uu____8018 > (Prims.parse_int "1")))
in (match (uu____8017) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____8031 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____8031) with
| None -> begin
[]
end
| uu____8042 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational None)
in (

let disc = (

let uu____8050 = (

let uu____8051 = (

let uu____8052 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (uu____8052)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____8051))
in (uu____8050 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (

let uu____8057 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (uu____8057)::[])))
end)))
end
| uu____8064 -> begin
[]
end)))
in (

let fail = (fun uu____8073 -> (

let uu____8074 = (

let uu____8075 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (

let uu____8076 = (FStar_Syntax_Print.term_to_string pat_exp)
in (

let uu____8077 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____8075 uu____8076 uu____8077))))
in (failwith uu____8074)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____8098) -> begin
(head_constructor t)
end
| uu____8104 -> begin
(fail ())
end))
in (

let pat_exp = (

let uu____8107 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right uu____8107 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____8123) -> begin
(

let uu____8124 = (

let uu____8127 = (

let uu____8128 = (

let uu____8129 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (

let uu____8130 = (

let uu____8132 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (uu____8132)::[])
in (uu____8129)::uu____8130))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq uu____8128))
in (uu____8127 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (uu____8124)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in (

let uu____8148 = (

let uu____8149 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____8149)))
in (match (uu____8148) with
| true -> begin
[]
end
| uu____8155 -> begin
(

let uu____8156 = (head_constructor pat_exp)
in (discriminate scrutinee_tm uu____8156))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in (

let uu____8183 = (

let uu____8184 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____8184)))
in (match (uu____8183) with
| true -> begin
[]
end
| uu____8190 -> begin
(

let sub_term_guards = (

let uu____8193 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____8209 -> (match (uu____8209) with
| (ei, uu____8216) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____8226 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____8226) with
| None -> begin
[]
end
| uu____8233 -> begin
(

let sub_term = (

let uu____8240 = (

let uu____8241 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (

let uu____8246 = (

let uu____8247 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (uu____8247)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____8241 uu____8246)))
in (uu____8240 None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____8193 FStar_List.flatten))
in (

let uu____8259 = (discriminate scrutinee_tm f)
in (FStar_List.append uu____8259 sub_term_guards)))
end)))
end
| uu____8267 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> (

let uu____8279 = (

let uu____8280 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8280)))
in (match (uu____8279) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end
| uu____8281 -> begin
(

let t = (

let uu____8283 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____8283))
in (

let uu____8286 = (FStar_Syntax_Util.type_u ())
in (match (uu____8286) with
| (k, uu____8290) -> begin
(

let uu____8291 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____8291) with
| (t, uu____8296, uu____8297) -> begin
t
end))
end)))
end)))
in (

let branch_guard = (

let uu____8299 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right uu____8299 FStar_Syntax_Util.mk_disj_l))
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

let uu____8316 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8316) with
| true -> begin
(

let uu____8317 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____8317))
end
| uu____8318 -> begin
()
end));
(

let uu____8319 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((uu____8319), (branch_guard), (c), (guard)));
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

let uu____8337 = (check_let_bound_def true env lb)
in (match (uu____8337) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let uu____8351 = (match ((annotated && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
((g1), (e1), (univ_vars), (c1))
end
| uu____8360 -> begin
(

let g1 = (

let uu____8362 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right uu____8362 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____8364 = (

let uu____8369 = (

let uu____8375 = (

let uu____8380 = (

let uu____8388 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____8388)))
in (uu____8380)::[])
in (FStar_TypeChecker_Util.generalize env uu____8375))
in (FStar_List.hd uu____8369))
in (match (uu____8364) with
| (uu____8417, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end)
in (match (uu____8351) with
| (g1, e1, univ_vars, c1) -> begin
(

let uu____8428 = (

let uu____8433 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____8433) with
| true -> begin
(

let uu____8438 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (uu____8438) with
| (ok, c1) -> begin
(match (ok) with
| true -> begin
((e2), (c1))
end
| uu____8453 -> begin
((

let uu____8455 = (FStar_Options.warn_top_level_effects ())
in (match (uu____8455) with
| true -> begin
(

let uu____8456 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.warn uu____8456 FStar_TypeChecker_Err.top_level_effect))
end
| uu____8457 -> begin
()
end));
(

let uu____8458 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))))) None e2.FStar_Syntax_Syntax.pos)
in ((uu____8458), (c1)));
)
end)
end))
end
| uu____8473 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let c = (

let uu____8476 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right uu____8476 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c)));
)
end))
in (match (uu____8428) with
| (e2, c1) -> begin
(

let cres = (

let uu____8493 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8493))
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (

let uu____8504 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((uu____8504), (cres), (FStar_TypeChecker_Rel.trivial_guard))));
))
end))
end))
end))
end
| uu____8523 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let uu___111_8544 = env
in {FStar_TypeChecker_Env.solver = uu___111_8544.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_8544.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_8544.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_8544.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_8544.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_8544.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_8544.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_8544.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_8544.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_8544.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_8544.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_8544.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_8544.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___111_8544.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_8544.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_8544.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_8544.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___111_8544.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___111_8544.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___111_8544.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_8544.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_8544.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_8544.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____8545 = (

let uu____8551 = (

let uu____8552 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____8552 Prims.fst))
in (check_let_bound_def false uu____8551 lb))
in (match (uu____8545) with
| (e1, uu____8564, c1, g1, annotated) -> begin
(

let x = (

let uu___112_8569 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___112_8569.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_8569.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____8570 = (

let uu____8573 = (

let uu____8574 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____8574)::[])
in (FStar_Syntax_Subst.open_term uu____8573 e2))
in (match (uu____8570) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let uu____8586 = (

let uu____8590 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term uu____8590 e2))
in (match (uu____8586) with
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

let uu____8605 = (

let uu____8608 = (

let uu____8609 = (

let uu____8617 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (uu____8617)))
in FStar_Syntax_Syntax.Tm_let (uu____8609))
in (FStar_Syntax_Syntax.mk uu____8608))
in (uu____8605 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____8632 = (

let uu____8633 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ uu____8633 e1))
in (FStar_All.pipe_left (fun _0_32 -> FStar_TypeChecker_Common.NonTrivial (_0_32)) uu____8632))
in (

let g2 = (

let uu____8639 = (

let uu____8640 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____8640 g2))
in (FStar_TypeChecker_Rel.close_guard xb uu____8639))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (

let uu____8642 = (

let uu____8643 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome uu____8643))
in (match (uu____8642) with
| true -> begin
(

let tt = (

let uu____8649 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right uu____8649 FStar_Option.get))
in ((

let uu____8653 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____8653) with
| true -> begin
(

let uu____8654 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____8655 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____8654 uu____8655)))
end
| uu____8656 -> begin
()
end));
((e), (cres), (guard));
))
end
| uu____8657 -> begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____8660 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____8660) with
| true -> begin
(

let uu____8661 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____8662 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____8661 uu____8662)))
end
| uu____8663 -> begin
()
end));
((e), ((

let uu___113_8664 = cres
in {FStar_Syntax_Syntax.eff_name = uu___113_8664.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___113_8664.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___113_8664.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____8665 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8686 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8686) with
| (lbs, e2) -> begin
(

let uu____8697 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8697) with
| (env0, topt) -> begin
(

let uu____8708 = (build_let_rec_env true env0 lbs)
in (match (uu____8708) with
| (lbs, rec_env) -> begin
(

let uu____8719 = (check_let_recs rec_env lbs)
in (match (uu____8719) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (

let uu____8731 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right uu____8731 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (

let uu____8735 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____8735 (fun _0_33 -> Some (_0_33))))
in (

let lbs = (match ((not (env.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (match ((lb.FStar_Syntax_Syntax.lbunivs = [])) with
| true -> begin
lb
end
| uu____8751 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end))))
end
| uu____8752 -> begin
(

let ecs = (

let uu____8759 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____8781 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____8781))))))
in (FStar_TypeChecker_Util.generalize env uu____8759))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____8801 -> (match (uu____8801) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (

let uu____8826 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8826))
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let uu____8835 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____8835) with
| (lbs, e2) -> begin
(

let uu____8846 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____8861 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((uu____8846), (cres), (uu____8861))))
end));
)))))
end))
end))
end))
end))
end
| uu____8864 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8885 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8885) with
| (lbs, e2) -> begin
(

let uu____8896 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8896) with
| (env0, topt) -> begin
(

let uu____8907 = (build_let_rec_env false env0 lbs)
in (match (uu____8907) with
| (lbs, rec_env) -> begin
(

let uu____8918 = (check_let_recs rec_env lbs)
in (match (uu____8918) with
| (lbs, g_lbs) -> begin
(

let uu____8929 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let uu___114_8940 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___114_8940.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_8940.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let uu___115_8942 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___115_8942.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___115_8942.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___115_8942.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___115_8942.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (uu____8929) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____8959 = (tc_term env e2)
in (match (uu____8959) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___116_8973 = cres
in {FStar_Syntax_Syntax.eff_name = uu___116_8973.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___116_8973.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___116_8973.FStar_Syntax_Syntax.comp})
in (

let uu____8974 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____8974) with
| (lbs, e2) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (uu____9003) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let uu___117_9008 = cres
in {FStar_Syntax_Syntax.eff_name = uu___117_9008.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___117_9008.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___117_9008.FStar_Syntax_Syntax.comp})
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
| uu____9011 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let uu____9027 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____9027) with
| (uu____9033, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let uu____9044 = (FStar_List.fold_left (fun uu____9051 lb -> (match (uu____9051) with
| (lbs, env) -> begin
(

let uu____9063 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (uu____9063) with
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
| uu____9076 -> begin
(

let uu____9077 = (

let uu____9081 = (

let uu____9082 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst uu____9082))
in (tc_check_tot_or_gtot_term (

let uu___118_9087 = env0
in {FStar_TypeChecker_Env.solver = uu___118_9087.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___118_9087.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___118_9087.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___118_9087.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___118_9087.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___118_9087.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___118_9087.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___118_9087.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___118_9087.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___118_9087.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___118_9087.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___118_9087.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___118_9087.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___118_9087.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___118_9087.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___118_9087.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___118_9087.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___118_9087.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___118_9087.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___118_9087.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___118_9087.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___118_9087.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___118_9087.FStar_TypeChecker_Env.qname_and_index}) t uu____9081))
in (match (uu____9077) with
| (t, uu____9089, g) -> begin
(

let g = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((

let uu____9093 = (FStar_TypeChecker_Rel.discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore uu____9093));
(norm env0 t);
))
end))
end)
in (

let env = (

let uu____9095 = ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env))
in (match (uu____9095) with
| true -> begin
(

let uu___119_9096 = env
in {FStar_TypeChecker_Env.solver = uu___119_9096.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_9096.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_9096.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_9096.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_9096.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_9096.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_9096.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_9096.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_9096.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_9096.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_9096.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_9096.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_9096.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_9096.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_9096.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_9096.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_9096.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___119_9096.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___119_9096.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___119_9096.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_9096.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_9096.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_9096.FStar_TypeChecker_Env.qname_and_index})
end
| uu____9103 -> begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end))
in (

let lb = (

let uu___120_9106 = lb
in {FStar_Syntax_Syntax.lbname = uu___120_9106.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___120_9106.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____9044) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____9120 = (

let uu____9125 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____9136 = (

let uu____9140 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____9140 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____9136) with
| (e, c, g) -> begin
((

let uu____9147 = (

let uu____9148 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____9148)))
in (match (uu____9147) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____9149 -> begin
()
end));
(

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g)));
)
end)))))
in (FStar_All.pipe_right uu____9125 FStar_List.unzip))
in (match (uu____9120) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____9177 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9177) with
| (env1, uu____9187) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____9193 = (check_lbtyp top_level env lb)
in (match (uu____9193) with
| (topt, wf_annot, univ_vars, univ_opening, env1) -> begin
((match (((not (top_level)) && (univ_vars <> []))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____9216 -> begin
()
end);
(

let e1 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____9219 = (tc_maybe_toplevel_term (

let uu___121_9223 = env1
in {FStar_TypeChecker_Env.solver = uu___121_9223.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___121_9223.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___121_9223.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___121_9223.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___121_9223.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___121_9223.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___121_9223.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___121_9223.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___121_9223.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___121_9223.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___121_9223.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___121_9223.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___121_9223.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___121_9223.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___121_9223.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___121_9223.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___121_9223.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___121_9223.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___121_9223.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___121_9223.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___121_9223.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___121_9223.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___121_9223.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (uu____9219) with
| (e1, c1, g1) -> begin
(

let uu____9232 = (

let uu____9235 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____9238 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____9235 e1 c1 wf_annot))
in (match (uu____9232) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____9248 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9248) with
| true -> begin
(

let uu____9249 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____9250 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____9251 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" uu____9249 uu____9250 uu____9251))))
end
| uu____9252 -> begin
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
| uu____9273 -> begin
()
end);
((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____9277 -> begin
(

let uu____9278 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____9278) with
| (univ_opening, univ_vars) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____9305 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (univ_opening), (uu____9305)))
end
| uu____9309 -> begin
(

let uu____9310 = (FStar_Syntax_Util.type_u ())
in (match (uu____9310) with
| (k, uu____9321) -> begin
(

let uu____9322 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____9322) with
| (t, uu____9334, g) -> begin
((

let uu____9337 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____9337) with
| true -> begin
(

let uu____9338 = (

let uu____9339 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____9339))
in (

let uu____9340 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____9338 uu____9340)))
end
| uu____9341 -> begin
()
end));
(

let t = (norm env1 t)
in (

let uu____9343 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (univ_opening), (uu____9343))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____9348 -> (match (uu____9348) with
| (x, imp) -> begin
(

let uu____9359 = (FStar_Syntax_Util.type_u ())
in (match (uu____9359) with
| (tu, u) -> begin
((

let uu____9371 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9371) with
| true -> begin
(

let uu____9372 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____9373 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____9374 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____9372 uu____9373 uu____9374))))
end
| uu____9375 -> begin
()
end));
(

let uu____9376 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____9376) with
| (t, uu____9387, g) -> begin
(

let x = (((

let uu___122_9392 = x
in {FStar_Syntax_Syntax.ppname = uu___122_9392.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___122_9392.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____9394 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____9394) with
| true -> begin
(

let uu____9395 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (

let uu____9396 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____9395 uu____9396)))
end
| uu____9397 -> begin
()
end));
(

let uu____9398 = (push_binding env x)
in ((x), (uu____9398), (g), (u)));
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

let uu____9449 = (tc_binder env b)
in (match (uu____9449) with
| (b, env', g, u) -> begin
(

let uu____9472 = (aux env' bs)
in (match (uu____9472) with
| (bs, env', g', us) -> begin
(

let uu____9501 = (

let uu____9502 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____9502))
in (((b)::bs), (env'), (uu____9501), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun uu____9548 uu____9549 -> (match (((uu____9548), (uu____9549))) with
| ((t, imp), (args, g)) -> begin
(

let uu____9586 = (tc_term env t)
in (match (uu____9586) with
| (t, uu____9596, g') -> begin
(

let uu____9598 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (uu____9598)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____9619 -> (match (uu____9619) with
| (pats, g) -> begin
(

let uu____9645 = (tc_args env p)
in (match (uu____9645) with
| (args, g') -> begin
(

let uu____9665 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (uu____9665)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____9685 = (tc_maybe_toplevel_term env e)
in (match (uu____9685) with
| (e, c, g) -> begin
(

let uu____9695 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____9695) with
| true -> begin
((e), (c), (g))
end
| uu____9699 -> begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let c = (norm_c env c)
in (

let uu____9705 = (

let uu____9708 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c))
in (match (uu____9708) with
| true -> begin
(

let uu____9711 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((uu____9711), (false)))
end
| uu____9712 -> begin
(

let uu____9713 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((uu____9713), (true)))
end))
in (match (uu____9705) with
| (target_comp, allow_ghost) -> begin
(

let uu____9719 = (FStar_TypeChecker_Rel.sub_comp env c target_comp)
in (match (uu____9719) with
| Some (g') -> begin
(

let uu____9725 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (uu____9725)))
end
| uu____9726 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____9731 = (

let uu____9732 = (

let uu____9735 = (FStar_TypeChecker_Err.expected_ghost_expression e c)
in ((uu____9735), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____9732))
in (Prims.raise uu____9731))
end
| uu____9739 -> begin
(

let uu____9740 = (

let uu____9741 = (

let uu____9744 = (FStar_TypeChecker_Err.expected_pure_expression e c)
in ((uu____9744), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____9741))
in (Prims.raise uu____9740))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____9757 = (tc_tot_or_gtot_term env t)
in (match (uu____9757) with
| (t, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____9777 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____9777) with
| true -> begin
(

let uu____9778 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____9778))
end
| uu____9779 -> begin
()
end));
(

let env = (

let uu___123_9781 = env
in {FStar_TypeChecker_Env.solver = uu___123_9781.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___123_9781.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___123_9781.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___123_9781.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___123_9781.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___123_9781.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___123_9781.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___123_9781.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___123_9781.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___123_9781.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___123_9781.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___123_9781.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___123_9781.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___123_9781.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___123_9781.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___123_9781.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___123_9781.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___123_9781.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___123_9781.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___123_9781.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___123_9781.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___123_9781.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___123_9781.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____9782 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Errors.Error (msg, uu____9798) -> begin
(

let uu____9799 = (

let uu____9800 = (

let uu____9803 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (uu____9803)))
in FStar_Errors.Error (uu____9800))
in (Prims.raise uu____9799))
end
in (match (uu____9782) with
| (t, c, g) -> begin
(

let uu____9813 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____9813) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____9819 -> begin
(

let uu____9820 = (

let uu____9821 = (

let uu____9824 = (

let uu____9825 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____9825))
in (

let uu____9826 = (FStar_TypeChecker_Env.get_range env)
in ((uu____9824), (uu____9826))))
in FStar_Errors.Error (uu____9821))
in (Prims.raise uu____9820))
end))
end)));
))


let level_of_type_fail = (fun env e t -> (

let uu____9847 = (

let uu____9848 = (

let uu____9851 = (

let uu____9852 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____9852 t))
in (

let uu____9853 = (FStar_TypeChecker_Env.get_range env)
in ((uu____9851), (uu____9853))))
in FStar_Errors.Error (uu____9848))
in (Prims.raise uu____9847)))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t -> (

let uu____9870 = (

let uu____9871 = (FStar_Syntax_Util.unrefine t)
in uu____9871.FStar_Syntax_Syntax.n)
in (match (uu____9870) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____9875 -> begin
(match (retry) with
| true -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (aux false t))
end
| uu____9877 -> begin
(

let uu____9878 = (FStar_Syntax_Util.type_u ())
in (match (uu____9878) with
| (t_u, u) -> begin
(

let env = (

let uu___126_9884 = env
in {FStar_TypeChecker_Env.solver = uu___126_9884.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___126_9884.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___126_9884.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___126_9884.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___126_9884.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___126_9884.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___126_9884.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___126_9884.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___126_9884.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___126_9884.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___126_9884.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___126_9884.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___126_9884.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___126_9884.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___126_9884.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___126_9884.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___126_9884.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___126_9884.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___126_9884.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___126_9884.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___126_9884.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___126_9884.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___126_9884.FStar_TypeChecker_Env.qname_and_index})
in (

let g = (FStar_TypeChecker_Rel.teq env t t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____9888 = (FStar_Syntax_Print.term_to_string t)
in (level_of_type_fail env e uu____9888))
end
| uu____9889 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____9898 = (

let uu____9899 = (FStar_Syntax_Subst.compress e)
in uu____9899.FStar_Syntax_Syntax.n)
in (match (uu____9898) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____9908) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____9919) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____9944, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____9959) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n) -> begin
n.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____9966 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9966) with
| (uu____9975, t) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____9977, FStar_Util.Inl (t), uu____9979) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____9998, FStar_Util.Inr (c), uu____10000) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u)))) None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____10030; FStar_Syntax_Syntax.pos = uu____10031; FStar_Syntax_Syntax.vars = uu____10032}, us) -> begin
(

let uu____10038 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10038) with
| (us', t) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____10054 = (

let uu____10055 = (

let uu____10058 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____10058)))
in FStar_Errors.Error (uu____10055))
in (Prims.raise uu____10054))
end
| uu____10059 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____10066 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____10067) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____10075) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____10092 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____10092) with
| (bs, c) -> begin
(

let us = (FStar_List.map (fun uu____10103 -> (match (uu____10103) with
| (b, uu____10107) -> begin
(

let uu____10108 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____10108))
end)) bs)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c)
in (

let uu____10113 = (universe_of_aux env res)
in (level_of_type env res uu____10113)))
in (

let u_c = (

let uu____10115 = (FStar_TypeChecker_Util.effect_repr env c u_res)
in (match (uu____10115) with
| None -> begin
u_res
end
| Some (trepr) -> begin
(

let uu____10118 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____10118))
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

let uu____10204 = (universe_of_aux env hd)
in ((uu____10204), (args)))
end
| FStar_Syntax_Syntax.Tm_match (uu____10214, (hd)::uu____10216) -> begin
(

let uu____10263 = (FStar_Syntax_Subst.open_branch hd)
in (match (uu____10263) with
| (uu____10273, uu____10274, hd) -> begin
(

let uu____10290 = (FStar_Syntax_Util.head_and_args hd)
in (match (uu____10290) with
| (hd, args) -> begin
(type_of_head retry hd args)
end))
end))
end
| uu____10325 when retry -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____10327 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____10327) with
| (hd, args) -> begin
(type_of_head false hd args)
end)))
end
| uu____10362 -> begin
(

let uu____10363 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____10363) with
| (env, uu____10377) -> begin
(

let env = (

let uu___127_10381 = env
in {FStar_TypeChecker_Env.solver = uu___127_10381.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___127_10381.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___127_10381.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___127_10381.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___127_10381.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___127_10381.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___127_10381.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___127_10381.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___127_10381.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___127_10381.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___127_10381.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___127_10381.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___127_10381.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___127_10381.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___127_10381.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___127_10381.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___127_10381.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___127_10381.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___127_10381.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___127_10381.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___127_10381.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____10383 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("UniverseOf")))
in (match (uu____10383) with
| true -> begin
(

let uu____10384 = (

let uu____10385 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____10385))
in (

let uu____10386 = (FStar_Syntax_Print.term_to_string hd)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____10384 uu____10386)))
end
| uu____10387 -> begin
()
end));
(

let uu____10388 = (tc_term env hd)
in (match (uu____10388) with
| (uu____10401, {FStar_Syntax_Syntax.eff_name = uu____10402; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____10404; FStar_Syntax_Syntax.comp = uu____10405}, g) -> begin
((

let uu____10415 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____10415 Prims.ignore));
((t), (args));
)
end));
))
end))
end)))
in (

let uu____10423 = (type_of_head true hd args)
in (match (uu____10423) with
| (t, args) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____10452 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____10452) with
| (bs, res) -> begin
(

let res = (FStar_Syntax_Util.comp_result res)
in (match (((FStar_List.length bs) = (FStar_List.length args))) with
| true -> begin
(

let subst = (FStar_Syntax_Util.subst_of_list bs args)
in (FStar_Syntax_Subst.subst subst res))
end
| uu____10484 -> begin
(

let uu____10485 = (FStar_Syntax_Print.term_to_string res)
in (level_of_type_fail env e uu____10485))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____10488, (hd)::uu____10490) -> begin
(

let uu____10537 = (FStar_Syntax_Subst.open_branch hd)
in (match (uu____10537) with
| (uu____10540, uu____10541, hd) -> begin
(universe_of_aux env hd)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____10557, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____10591 = (universe_of_aux env e)
in (level_of_type env e uu____10591)))




