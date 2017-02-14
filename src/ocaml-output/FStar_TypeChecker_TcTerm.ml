
open Prims

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___81_4 = env
in {FStar_TypeChecker_Env.solver = uu___81_4.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___81_4.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___81_4.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___81_4.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___81_4.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___81_4.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___81_4.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___81_4.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___81_4.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___81_4.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___81_4.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___81_4.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___81_4.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___81_4.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___81_4.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___81_4.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___81_4.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___81_4.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___81_4.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___81_4.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___81_4.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___81_4.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___81_4.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___82_8 = env
in {FStar_TypeChecker_Env.solver = uu___82_8.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___82_8.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___82_8.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___82_8.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___82_8.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___82_8.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___82_8.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___82_8.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___82_8.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___82_8.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___82_8.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___82_8.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___82_8.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___82_8.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___82_8.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___82_8.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___82_8.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___82_8.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___82_8.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___82_8.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___82_8.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___82_8.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___82_8.FStar_TypeChecker_Env.qname_and_index}))


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

let uu___83_181 = lc
in {FStar_Syntax_Syntax.eff_name = uu___83_181.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___83_181.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____182 -> (

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

let uu___84_645 = env
in {FStar_TypeChecker_Env.solver = uu___84_645.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___84_645.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___84_645.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___84_645.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___84_645.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___84_645.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___84_645.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___84_645.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___84_645.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___84_645.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___84_645.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___84_645.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___84_645.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___84_645.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___84_645.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___84_645.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___84_645.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___84_645.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___84_645.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___84_645.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___84_645.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___84_645.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___84_645.FStar_TypeChecker_Env.qname_and_index})
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

let uu___85_852 = last
in (

let uu____853 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = uu___85_852.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___85_852.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____853}))
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

let uu___86_1141 = env
in {FStar_TypeChecker_Env.solver = uu___86_1141.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___86_1141.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___86_1141.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___86_1141.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___86_1141.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___86_1141.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___86_1141.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___86_1141.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___86_1141.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___86_1141.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___86_1141.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___86_1141.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___86_1141.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___86_1141.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___86_1141.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___86_1141.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___86_1141.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___86_1141.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___86_1141.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___86_1141.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___86_1141.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___86_1141.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___86_1141.FStar_TypeChecker_Env.qname_and_index}) e))
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

let uu___87_1209 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___87_1209.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___87_1209.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___87_1209.FStar_TypeChecker_Env.implicits})
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

let uu___88_1283 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___88_1283.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___88_1283.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___88_1283.FStar_TypeChecker_Env.implicits})
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

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____1407 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (uu____1407))))))
end))
end))
end
| uu____1410 -> begin
(

let uu____1411 = (tc_term env e)
in (match (uu____1411) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____1435)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let uu____1450 = (tc_term env e)
in (match (uu____1450) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), uu____1475) -> begin
(

let uu____1494 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1494) with
| (env0, uu____1502) -> begin
(

let uu____1505 = (tc_comp env0 expected_c)
in (match (uu____1505) with
| (expected_c, uu____1513, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let uu____1518 = (

let uu____1522 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____1522 e))
in (match (uu____1518) with
| (e, c', g') -> begin
(

let uu____1529 = (

let uu____1533 = (

let uu____1536 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (uu____1536)))
in (check_expected_effect env0 (Some (expected_c)) uu____1533))
in (match (uu____1529) with
| (e, expected_c, g'') -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c))))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (

let uu____1571 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____1571))
in (

let uu____1572 = (comp_check_expected_typ env e lc)
in (match (uu____1572) with
| (e, c, f2) -> begin
(

let uu____1582 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (uu____1582)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), uu____1585) -> begin
(

let uu____1604 = (FStar_Syntax_Util.type_u ())
in (match (uu____1604) with
| (k, u) -> begin
(

let uu____1612 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____1612) with
| (t, uu____1620, f) -> begin
(

let uu____1622 = (

let uu____1626 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term uu____1626 e))
in (match (uu____1622) with
| (e, c, g) -> begin
(

let uu____1633 = (

let uu____1636 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____1639 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____1636 e c f))
in (match (uu____1633) with
| (c, f) -> begin
(

let uu____1645 = (

let uu____1649 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name)))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env uu____1649 c))
in (match (uu____1645) with
| (e, c, f2) -> begin
(

let uu____1671 = (

let uu____1672 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f uu____1672))
in ((e), (c), (uu____1671)))
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

let uu____1749 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1749) with
| (unary_op, uu____1763) -> begin
(

let head = (

let uu____1781 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[]))))) None uu____1781))
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest))))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____1825; FStar_Syntax_Syntax.pos = uu____1826; FStar_Syntax_Syntax.vars = uu____1827}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____1852 -> begin
()
end);
(

let uu____1853 = (

let uu____1857 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1857) with
| (env0, uu____1865) -> begin
(tc_term env0 e)
end))
in (match (uu____1853) with
| (e, c, g) -> begin
(

let uu____1874 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1874) with
| (reify_op, uu____1888) -> begin
(

let u_c = (

let uu____1904 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (uu____1904) with
| (uu____1908, c, uu____1910) -> begin
(

let uu____1911 = (

let uu____1912 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in uu____1912.FStar_Syntax_Syntax.n)
in (match (uu____1911) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____1916 -> begin
(failwith "Unexpected result type of computation")
end))
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[]))))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (

let uu____1939 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____1939 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____1940 = (comp_check_expected_typ env e c)
in (match (uu____1940) with
| (e, c, g') -> begin
(

let uu____1950 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (uu____1950)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = uu____1952; FStar_Syntax_Syntax.pos = uu____1953; FStar_Syntax_Syntax.vars = uu____1954}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____1979 -> begin
()
end);
(

let no_reflect = (fun uu____1986 -> (

let uu____1987 = (

let uu____1988 = (

let uu____1991 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((uu____1991), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____1988))
in (Prims.raise uu____1987)))
in (

let uu____1995 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1995) with
| (reflect_op, uu____2009) -> begin
(

let uu____2024 = (FStar_TypeChecker_Env.effect_decl_opt env l)
in (match (uu____2024) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
(

let uu____2030 = (

let uu____2031 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____2031)))
in (match (uu____2030) with
| true -> begin
(no_reflect ())
end
| uu____2036 -> begin
(

let uu____2037 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2037) with
| (env_no_ex, topt) -> begin
(

let uu____2048 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____2063 = (

let uu____2066 = (

let uu____2067 = (

let uu____2077 = (

let uu____2079 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____2080 = (

let uu____2082 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____2082)::[])
in (uu____2079)::uu____2080))
in ((repr), (uu____2077)))
in FStar_Syntax_Syntax.Tm_app (uu____2067))
in (FStar_Syntax_Syntax.mk uu____2066))
in (uu____2063 None top.FStar_Syntax_Syntax.pos))
in (

let uu____2092 = (

let uu____2096 = (

let uu____2097 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____2097 Prims.fst))
in (tc_tot_or_gtot_term uu____2096 t))
in (match (uu____2092) with
| (t, uu____2114, g) -> begin
(

let uu____2116 = (

let uu____2117 = (FStar_Syntax_Subst.compress t)
in uu____2117.FStar_Syntax_Syntax.n)
in (match (uu____2116) with
| FStar_Syntax_Syntax.Tm_app (uu____2128, ((res, uu____2130))::((wp, uu____2132))::[]) -> begin
((t), (res), (wp), (g))
end
| uu____2166 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____2048) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____2190 = (

let uu____2193 = (tc_tot_or_gtot_term env_no_ex e)
in (match (uu____2193) with
| (e, c, g) -> begin
((

let uu____2203 = (

let uu____2204 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____2204))
in (match (uu____2203) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____2209 -> begin
()
end));
(

let uu____2210 = (FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____2210) with
| None -> begin
((

let uu____2215 = (

let uu____2219 = (

let uu____2222 = (

let uu____2223 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2224 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____2223 uu____2224)))
in ((uu____2222), (e.FStar_Syntax_Syntax.pos)))
in (uu____2219)::[])
in (FStar_TypeChecker_Err.add_errors env uu____2215));
(

let uu____2229 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (uu____2229)));
)
end
| Some (g') -> begin
(

let uu____2231 = (

let uu____2232 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____2232))
in ((e), (uu____2231)))
end));
)
end))
in (match (uu____2190) with
| (e, g) -> begin
(

let c = (

let uu____2239 = (

let uu____2240 = (

let uu____2241 = (

let uu____2242 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (uu____2242)::[])
in (

let uu____2243 = (

let uu____2249 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2249)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____2241; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____2243; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____2240))
in (FStar_All.pipe_right uu____2239 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[]))))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____2270 = (comp_check_expected_typ env e c)
in (match (uu____2270) with
| (e, c, g') -> begin
(

let uu____2280 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (uu____2280)))
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

let uu____2299 = (

let uu____2300 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____2300 Prims.fst))
in (FStar_All.pipe_right uu____2299 instantiate_both))
in ((

let uu____2309 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____2309) with
| true -> begin
(

let uu____2310 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____2311 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____2310 uu____2311)))
end
| uu____2312 -> begin
()
end));
(

let uu____2313 = (tc_term (no_inst env) head)
in (match (uu____2313) with
| (head, chead, g_head) -> begin
(

let uu____2323 = (

let uu____2327 = ((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head))
in (match (uu____2327) with
| true -> begin
(

let uu____2331 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args uu____2331))
end
| uu____2333 -> begin
(

let uu____2334 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args uu____2334))
end))
in (match (uu____2323) with
| (e, c, g) -> begin
((

let uu____2343 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2343) with
| true -> begin
(

let uu____2344 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____2344))
end
| uu____2345 -> begin
()
end));
(

let c = (

let uu____2347 = (((FStar_TypeChecker_Env.should_verify env) && (

let uu____2348 = (FStar_Syntax_Util.is_lcomp_partial_return c)
in (not (uu____2348)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____2347) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end
| uu____2349 -> begin
c
end))
in (

let uu____2350 = (comp_check_expected_typ env0 e c)
in (match (uu____2350) with
| (e, c, g') -> begin
(

let gimp = (

let uu____2361 = (

let uu____2362 = (FStar_Syntax_Subst.compress head)
in uu____2362.FStar_Syntax_Syntax.n)
in (match (uu____2361) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____2366) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let uu___89_2398 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___89_2398.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___89_2398.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___89_2398.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____2423 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (

let uu____2425 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g uu____2425))
in ((

let uu____2427 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2427) with
| true -> begin
(

let uu____2428 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____2429 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____2428 uu____2429)))
end
| uu____2430 -> begin
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

let uu____2459 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2459) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let uu____2471 = (tc_term env1 e1)
in (match (uu____2471) with
| (e1, c1, g1) -> begin
(

let uu____2481 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let uu____2487 = (FStar_Syntax_Util.type_u ())
in (match (uu____2487) with
| (k, uu____2493) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (

let uu____2495 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((uu____2495), (res_t))))
end))
end)
in (match (uu____2481) with
| (env_branches, res_t) -> begin
((

let uu____2502 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2502) with
| true -> begin
(

let uu____2503 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____2503))
end
| uu____2504 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____2554 = (

let uu____2557 = (FStar_List.fold_right (fun uu____2576 uu____2577 -> (match (((uu____2576), (uu____2577))) with
| ((uu____2609, f, c, g), (caccum, gaccum)) -> begin
(

let uu____2642 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (uu____2642)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____2557) with
| (cases, g) -> begin
(

let uu____2663 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((uu____2663), (g)))
end))
in (match (uu____2554) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let scrutinee = (FStar_TypeChecker_Util.maybe_lift env scrutinee c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____2713 -> (match (uu____2713) with
| ((pat, wopt, br), uu____2729, lc, uu____2731) -> begin
(

let uu____2738 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (uu____2738)))
end))))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name)))))) None e.FStar_Syntax_Syntax.pos)))))
in (

let uu____2777 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____2777) with
| true -> begin
(mk_match e1)
end
| uu____2780 -> begin
(

let e_match = (

let uu____2784 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____2784))
in (

let lb = (

let uu____2786 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = uu____2786; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = (

let uu____2790 = (

let uu____2793 = (

let uu____2794 = (

let uu____2802 = (

let uu____2803 = (

let uu____2804 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____2804)::[])
in (FStar_Syntax_Subst.close uu____2803 e_match))
in ((((false), ((lb)::[]))), (uu____2802)))
in FStar_Syntax_Syntax.Tm_let (uu____2794))
in (FStar_Syntax_Syntax.mk uu____2793))
in (uu____2790 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____2818 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2818) with
| true -> begin
(

let uu____2819 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____2820 = (

let uu____2821 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2821))
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____2819 uu____2820)))
end
| uu____2822 -> begin
()
end));
(

let uu____2823 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (uu____2823)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2826); FStar_Syntax_Syntax.lbunivs = uu____2827; FStar_Syntax_Syntax.lbtyp = uu____2828; FStar_Syntax_Syntax.lbeff = uu____2829; FStar_Syntax_Syntax.lbdef = uu____2830})::[]), uu____2831) -> begin
((

let uu____2846 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2846) with
| true -> begin
(

let uu____2847 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____2847))
end
| uu____2848 -> begin
()
end));
(check_top_level_let env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____2849), uu____2850) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2860); FStar_Syntax_Syntax.lbunivs = uu____2861; FStar_Syntax_Syntax.lbtyp = uu____2862; FStar_Syntax_Syntax.lbeff = uu____2863; FStar_Syntax_Syntax.lbdef = uu____2864})::uu____2865), uu____2866) -> begin
((

let uu____2882 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2882) with
| true -> begin
(

let uu____2883 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____2883))
end
| uu____2884 -> begin
()
end));
(check_top_level_let_rec env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____2885), uu____2886) -> begin
(check_inner_let_rec env top)
end));
)))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let uu____2930 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____2930) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____2943 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2943) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____2946 -> begin
(

let uu____2947 = (

let uu____2948 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____2948))
in FStar_Util.Inr (uu____2947))
end))
in (

let is_data_ctor = (fun uu___78_2957 -> (match (uu___78_2957) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| uu____2960 -> begin
false
end))
in (

let uu____2962 = ((is_data_ctor dc) && (

let uu____2963 = (FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)
in (not (uu____2963))))
in (match (uu____2962) with
| true -> begin
(

let uu____2969 = (

let uu____2970 = (

let uu____2973 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____2976 = (FStar_TypeChecker_Env.get_range env)
in ((uu____2973), (uu____2976))))
in FStar_Errors.Error (uu____2970))
in (Prims.raise uu____2969))
end
| uu____2980 -> begin
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

let uu____2987 = (

let uu____2988 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____2988))
in (failwith uu____2987))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____3007 = (

let uu____3008 = (FStar_Syntax_Subst.compress t1)
in uu____3008.FStar_Syntax_Syntax.n)
in (match (uu____3007) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3011) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____3019 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___90_3039 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___90_3039.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___90_3039.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___90_3039.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3067 = (

let uu____3074 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____3074) with
| None -> begin
(

let uu____3082 = (FStar_Syntax_Util.type_u ())
in (match (uu____3082) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____3067) with
| (t, uu____3103, g0) -> begin
(

let uu____3111 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (uu____3111) with
| (e, uu____3122, g1) -> begin
(

let uu____3130 = (

let uu____3131 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____3131 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____3132 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (uu____3130), (uu____3132))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (match (env.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____3139 -> begin
(FStar_TypeChecker_Env.lookup_bv env x)
end)
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let uu___91_3141 = x
in {FStar_Syntax_Syntax.ppname = uu___91_3141.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___91_3141.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let uu____3142 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____3142) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____3155 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____3155) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____3158 -> begin
(

let uu____3159 = (

let uu____3160 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3160))
in FStar_Util.Inr (uu____3159))
end))
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____3166; FStar_Syntax_Syntax.pos = uu____3167; FStar_Syntax_Syntax.vars = uu____3168}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let uu____3176 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3176) with
| (us', t) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____3193 = (

let uu____3194 = (

let uu____3197 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____3197)))
in FStar_Errors.Error (uu____3194))
in (Prims.raise uu____3193))
end
| uu____3198 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____3205 -> begin
(failwith "Impossible")
end)) us' us)
end);
(

let fv' = (

let uu___92_3207 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___93_3208 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___93_3208.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___93_3208.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___92_3207.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___92_3207.FStar_Syntax_Syntax.fv_qual})
in (

let e = (

let uu____3222 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3222 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3234 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3234) with
| (us, t) -> begin
((

let uu____3247 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Range")))
in (match (uu____3247) with
| true -> begin
(

let uu____3248 = (

let uu____3249 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____3249))
in (

let uu____3250 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____3251 = (

let uu____3252 = (

let uu____3253 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid uu____3253))
in (FStar_Range.string_of_range uu____3252))
in (

let uu____3254 = (

let uu____3255 = (

let uu____3256 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid uu____3256))
in (FStar_Range.string_of_use_range uu____3255))
in (

let uu____3257 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s" uu____3248 uu____3250 uu____3251 uu____3254 uu____3257))))))
end
| uu____3258 -> begin
()
end));
(

let fv' = (

let uu___94_3260 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___95_3261 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___95_3261.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___95_3261.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___94_3260.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___94_3260.FStar_Syntax_Syntax.fv_qual})
in (

let e = (

let uu____3275 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3275 us))
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

let uu____3311 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3311) with
| (bs, c) -> begin
(

let env0 = env
in (

let uu____3320 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3320) with
| (env, uu____3328) -> begin
(

let uu____3331 = (tc_binders env bs)
in (match (uu____3331) with
| (bs, env, g, us) -> begin
(

let uu____3343 = (tc_comp env c)
in (match (uu____3343) with
| (c, uc, f) -> begin
(

let e = (

let uu___96_3356 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = uu___96_3356.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___96_3356.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___96_3356.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env e bs c);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____3377 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g uu____3377))
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

let uu____3412 = (

let uu____3415 = (

let uu____3416 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3416)::[])
in (FStar_Syntax_Subst.open_term uu____3415 phi))
in (match (uu____3412) with
| (x, phi) -> begin
(

let env0 = env
in (

let uu____3423 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3423) with
| (env, uu____3431) -> begin
(

let uu____3434 = (

let uu____3441 = (FStar_List.hd x)
in (tc_binder env uu____3441))
in (match (uu____3434) with
| (x, env, f1, u) -> begin
((

let uu____3458 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____3458) with
| true -> begin
(

let uu____3459 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3460 = (FStar_Syntax_Print.term_to_string phi)
in (

let uu____3461 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____3459 uu____3460 uu____3461))))
end
| uu____3462 -> begin
()
end));
(

let uu____3463 = (FStar_Syntax_Util.type_u ())
in (match (uu____3463) with
| (t_phi, uu____3470) -> begin
(

let uu____3471 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (uu____3471) with
| (phi, uu____3479, f2) -> begin
(

let e = (

let uu___97_3484 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = uu___97_3484.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___97_3484.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___97_3484.FStar_Syntax_Syntax.vars})
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____3503 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____3503))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____3512) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in ((

let uu____3537 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3537) with
| true -> begin
(

let uu____3538 = (FStar_Syntax_Print.term_to_string (

let uu___98_3539 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = uu___98_3539.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___98_3539.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___98_3539.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____3538))
end
| uu____3557 -> begin
()
end));
(

let uu____3558 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3558) with
| (bs, body) -> begin
(tc_abs env top bs body)
end));
))
end
| uu____3566 -> begin
(

let uu____3567 = (

let uu____3568 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____3569 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____3568 uu____3569)))
in (failwith uu____3567))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (uu____3575) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (uu____3576, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (uu____3582, Some (uu____3583)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____3591) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (uu____3595) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (uu____3596) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____3597) -> begin
FStar_TypeChecker_Common.t_range
end
| uu____3598 -> begin
(Prims.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____3609) -> begin
(

let uu____3616 = (FStar_Syntax_Util.type_u ())
in (match (uu____3616) with
| (k, u) -> begin
(

let uu____3624 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3624) with
| (t, uu____3632, g) -> begin
(

let uu____3634 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((uu____3634), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____3636) -> begin
(

let uu____3643 = (FStar_Syntax_Util.type_u ())
in (match (uu____3643) with
| (k, u) -> begin
(

let uu____3651 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3651) with
| (t, uu____3659, g) -> begin
(

let uu____3661 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((uu____3661), (u), (g)))
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

let uu____3677 = (

let uu____3678 = (

let uu____3679 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____3679)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head uu____3678))
in (uu____3677 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____3684 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____3684) with
| (tc, uu____3692, f) -> begin
(

let uu____3694 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3694) with
| (head, args) -> begin
(

let comp_univs = (

let uu____3724 = (

let uu____3725 = (FStar_Syntax_Subst.compress head)
in uu____3725.FStar_Syntax_Syntax.n)
in (match (uu____3724) with
| FStar_Syntax_Syntax.Tm_uinst (uu____3728, us) -> begin
us
end
| uu____3734 -> begin
[]
end))
in (

let uu____3735 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3735) with
| (uu____3748, args) -> begin
(

let uu____3764 = (

let uu____3776 = (FStar_List.hd args)
in (

let uu____3785 = (FStar_List.tl args)
in ((uu____3776), (uu____3785))))
in (match (uu____3764) with
| (res, args) -> begin
(

let uu____3827 = (

let uu____3832 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___79_3842 -> (match (uu___79_3842) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____3848 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3848) with
| (env, uu____3855) -> begin
(

let uu____3858 = (tc_tot_or_gtot_term env e)
in (match (uu____3858) with
| (e, uu____3865, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____3832 FStar_List.unzip))
in (match (uu____3827) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let uu___99_3888 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___99_3888.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = uu___99_3888.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____3892 = (FStar_TypeChecker_Util.effect_repr env c u)
in (match (uu____3892) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____3895 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (uu____3895))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____3903) -> begin
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

let uu____3906 = (aux u)
in FStar_Syntax_Syntax.U_succ (uu____3906))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____3909 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____3909))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____3912 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____3913 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____3913 Prims.snd))
end
| uu____3918 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (

let uu____3939 = (

let uu____3940 = (

let uu____3943 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((uu____3943), (top.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____3940))
in (Prims.raise uu____3939)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun uu____3997 bs bs_expected -> (match (uu____3997) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
((match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(

let uu____4094 = (

let uu____4095 = (

let uu____4098 = (

let uu____4099 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____4099))
in (

let uu____4100 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((uu____4098), (uu____4100))))
in FStar_Errors.Error (uu____4095))
in (Prims.raise uu____4094))
end
| uu____4101 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____4105 = (

let uu____4108 = (

let uu____4109 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in uu____4109.FStar_Syntax_Syntax.n)
in (match (uu____4108) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____4114 -> begin
((

let uu____4116 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____4116) with
| true -> begin
(

let uu____4117 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" uu____4117))
end
| uu____4118 -> begin
()
end));
(

let uu____4119 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (uu____4119) with
| (t, uu____4126, g1) -> begin
(

let g2 = (

let uu____4129 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4130 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard uu____4129 "Type annotation on parameter incompatible with the expected type" uu____4130)))
in (

let g = (

let uu____4132 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____4132))
in ((t), (g))))
end));
)
end))
in (match (uu____4105) with
| (t, g) -> begin
(

let hd = (

let uu___100_4148 = hd
in {FStar_Syntax_Syntax.ppname = uu___100_4148.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___100_4148.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (

let uu____4157 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected uu____4157))
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
| uu____4253 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____4257 = (tc_binders env bs)
in (match (uu____4257) with
| (bs, envbody, g, uu____4276) -> begin
(

let uu____4277 = (

let uu____4282 = (

let uu____4283 = (FStar_Syntax_Subst.compress body)
in uu____4283.FStar_Syntax_Syntax.n)
in (match (uu____4282) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), uu____4292) -> begin
(

let uu____4311 = (tc_comp envbody c)
in (match (uu____4311) with
| (c, uu____4320, g') -> begin
(

let uu____4322 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (uu____4322)))
end))
end
| uu____4324 -> begin
((None), (body), (g))
end))
in (match (uu____4277) with
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

let uu____4374 = (

let uu____4375 = (FStar_Syntax_Subst.compress t)
in uu____4375.FStar_Syntax_Syntax.n)
in (match (uu____4374) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
((match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4406 -> begin
(failwith "Impossible")
end);
(

let uu____4410 = (tc_binders env bs)
in (match (uu____4410) with
| (bs, envbody, g, uu____4430) -> begin
(

let uu____4431 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____4431) with
| (envbody, uu____4448) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____4459) -> begin
(

let uu____4464 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (uu____4464) with
| (uu____4489, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____4525 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____4525) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun uu____4586 c_expected -> (match (uu____4586) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(

let uu____4647 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (uu____4647)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____4664 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total uu____4664))
in (

let uu____4665 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (uu____4665))))
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

let uu____4706 = (check_binders env more_bs bs_expected)
in (match (uu____4706) with
| (env, bs', more, guard', subst) -> begin
(

let uu____4733 = (

let uu____4749 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (uu____4749), (subst)))
in (handle_more uu____4733 c_expected))
end))
end
| uu____4758 -> begin
(

let uu____4759 = (

let uu____4760 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" uu____4760))
in (fail uu____4759 t))
end))
end
| uu____4768 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end))
end)
end))
in (

let uu____4776 = (check_binders env bs bs_expected)
in (handle_more uu____4776 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let uu___101_4814 = envbody
in {FStar_TypeChecker_Env.solver = uu___101_4814.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___101_4814.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___101_4814.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___101_4814.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___101_4814.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___101_4814.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___101_4814.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___101_4814.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___101_4814.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___101_4814.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___101_4814.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___101_4814.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___101_4814.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___101_4814.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___101_4814.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___101_4814.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___101_4814.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___101_4814.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___101_4814.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___101_4814.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___101_4814.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___101_4814.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___101_4814.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____4828 uu____4829 -> (match (((uu____4828), (uu____4829))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let uu____4854 = (

let uu____4858 = (

let uu____4859 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____4859 Prims.fst))
in (tc_term uu____4858 t))
in (match (uu____4854) with
| (t, uu____4871, uu____4872) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____4879 = (FStar_Syntax_Syntax.mk_binder (

let uu___102_4880 = x
in {FStar_Syntax_Syntax.ppname = uu___102_4880.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_4880.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____4879)::letrec_binders)
end
| uu____4881 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let uu____4884 = (check_actuals_against_formals env bs bs_expected)
in (match (uu____4884) with
| (envbody, bs, g, c) -> begin
(

let uu____4914 = (

let uu____4918 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____4918) with
| true -> begin
(mk_letrec_env envbody bs c)
end
| uu____4922 -> begin
((envbody), ([]))
end))
in (match (uu____4914) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| uu____4951 -> begin
(match ((not (norm))) with
| true -> begin
(

let uu____4964 = (unfold_whnf env t)
in (as_function_typ true uu____4964))
end
| uu____4965 -> begin
(

let uu____4966 = (expected_function_typ env None body)
in (match (uu____4966) with
| (uu____4990, bs, uu____4992, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end)
end)))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____5013 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____5013) with
| (env, topt) -> begin
((

let uu____5025 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5025) with
| true -> begin
(

let uu____5026 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____5026 (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____5028 -> begin
"false"
end)))
end
| uu____5029 -> begin
()
end));
(

let uu____5030 = (expected_function_typ env topt body)
in (match (uu____5030) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let uu____5060 = (tc_term (

let uu___103_5064 = envbody
in {FStar_TypeChecker_Env.solver = uu___103_5064.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___103_5064.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___103_5064.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___103_5064.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___103_5064.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___103_5064.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___103_5064.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___103_5064.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___103_5064.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___103_5064.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___103_5064.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___103_5064.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___103_5064.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___103_5064.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___103_5064.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___103_5064.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___103_5064.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___103_5064.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___103_5064.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___103_5064.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___103_5064.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___103_5064.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (uu____5060) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in ((

let uu____5073 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))
in (match (uu____5073) with
| true -> begin
(

let uu____5074 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (

let uu____5083 = (

let uu____5084 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____5084))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" uu____5074 uu____5083)))
end
| uu____5085 -> begin
()
end));
(

let uu____5086 = (

let uu____5090 = (

let uu____5093 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (uu____5093)))
in (check_expected_effect (

let uu___104_5098 = envbody
in {FStar_TypeChecker_Env.solver = uu___104_5098.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___104_5098.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___104_5098.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___104_5098.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___104_5098.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___104_5098.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___104_5098.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___104_5098.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___104_5098.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___104_5098.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___104_5098.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___104_5098.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___104_5098.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___104_5098.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___104_5098.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___104_5098.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___104_5098.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___104_5098.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___104_5098.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___104_5098.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___104_5098.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___104_5098.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___104_5098.FStar_TypeChecker_Env.qname_and_index}) c_opt uu____5090))
in (match (uu____5086) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = (

let uu____5107 = (env.FStar_TypeChecker_Env.top_level || (

let uu____5108 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____5108))))
in (match (uu____5107) with
| true -> begin
(

let uu____5109 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____5109))
end
| uu____5110 -> begin
(

let guard = (

let uu____5112 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) uu____5112))
in guard)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (

let uu____5119 = (

let uu____5126 = (

let uu____5132 = (FStar_All.pipe_right (FStar_Util.dflt cbody c_opt) FStar_Syntax_Util.lcomp_of_comp)
in (FStar_All.pipe_right uu____5132 (fun _0_29 -> FStar_Util.Inl (_0_29))))
in Some (uu____5126))
in (FStar_Syntax_Util.abs bs body uu____5119))
in (

let uu____5146 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5161) -> begin
((e), (t), (guard))
end
| uu____5169 -> begin
(

let uu____5170 = (match (use_teq) with
| true -> begin
(

let uu____5175 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (uu____5175)))
end
| uu____5176 -> begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end)
in (match (uu____5170) with
| (e, guard') -> begin
(

let uu____5182 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (uu____5182)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (uu____5146) with
| (e, tfun, guard) -> begin
(

let c = (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____5194 -> begin
(FStar_TypeChecker_Util.return_value env tfun e)
end)
in (

let uu____5195 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (uu____5195) with
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

let uu____5231 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5231) with
| true -> begin
(

let uu____5232 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (

let uu____5233 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____5232 uu____5233)))
end
| uu____5234 -> begin
()
end));
(

let monadic_application = (fun uu____5275 subst arg_comps_rev arg_rets guard fvs bs -> (match (uu____5275) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___105_5316 = cres
in {FStar_Syntax_Syntax.eff_name = uu___105_5316.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___105_5316.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___105_5316.FStar_Syntax_Syntax.comp})
in (

let uu____5317 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun uu___80_5344 -> (match (uu___80_5344) with
| (uu____5353, uu____5354, FStar_Util.Inl (uu____5355)) -> begin
false
end
| (uu____5366, uu____5367, FStar_Util.Inr (c)) -> begin
(

let uu____5377 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (not (uu____5377)))
end)))))
in (

let cres = (match (refine_with_equality) with
| true -> begin
(

let uu____5379 = ((FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets)) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env uu____5379 cres))
end
| uu____5388 -> begin
((

let uu____5390 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5390) with
| true -> begin
(

let uu____5391 = (FStar_Syntax_Print.term_to_string head)
in (

let uu____5392 = (FStar_Syntax_Print.lcomp_to_string cres)
in (

let uu____5393 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" uu____5391 uu____5392 uu____5393))))
end
| uu____5394 -> begin
()
end));
cres;
)
end)
in ((cres), (g))))))
end
| uu____5395 -> begin
(

let g = (

let uu____5400 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right uu____5400 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (

let uu____5401 = (

let uu____5402 = (

let uu____5405 = (

let uu____5406 = (

let uu____5407 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs uu____5407))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) uu____5406))
in (FStar_Syntax_Syntax.mk_Total uu____5405))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5402))
in ((uu____5401), (g))))
end)
in (match (uu____5317) with
| (cres, guard) -> begin
((

let uu____5418 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5418) with
| true -> begin
(

let uu____5419 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____5419))
end
| uu____5420 -> begin
()
end));
(

let uu____5421 = (FStar_List.fold_left (fun uu____5444 uu____5445 -> (match (((uu____5444), (uu____5445))) with
| ((args, out_c, monadic), ((e, q), x, c)) -> begin
(match (c) with
| FStar_Util.Inl (eff_name, arg_typ) -> begin
(

let uu____5535 = (

let uu____5539 = (

let uu____5542 = (FStar_TypeChecker_Util.maybe_lift env e eff_name out_c.FStar_Syntax_Syntax.eff_name arg_typ)
in ((uu____5542), (q)))
in (uu____5539)::args)
in ((uu____5535), (out_c), (monadic)))
end
| FStar_Util.Inr (c) -> begin
(

let monadic = (monadic || (

let uu____5552 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (not (uu____5552))))
in (

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c ((x), (out_c)))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (((((e), (q)))::args), (out_c), (monadic))))))
end)
end)) (([]), (cres), (false)) arg_comps_rev)
in (match (uu____5421) with
| (args, comp, monadic) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead ((None), (comp)))
in (

let app = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (

let uu____5589 = (monadic || (

let uu____5590 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp comp)
in (not (uu____5590))))
in (match (uu____5589) with
| true -> begin
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
end
| uu____5591 -> begin
app
end))
in (

let uu____5592 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (uu____5592) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____5650 bs args -> (match (uu____5650) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (uu____5745))))::rest, ((uu____5747, None))::uu____5748) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let uu____5785 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (uu____5785) with
| (varg, uu____5796, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (

let uu____5809 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____5809)))
in (

let uu____5810 = (

let uu____5832 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (FStar_Util.Inl (((FStar_Syntax_Const.effect_Tot_lid), (t))))))::outargs), ((arg)::arg_rets), (uu____5832), (fvs)))
in (tc_args head_info uu____5810 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| uu____5923 -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___106_5930 = x
in {FStar_Syntax_Syntax.ppname = uu___106_5930.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___106_5930.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____5932 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____5932) with
| true -> begin
(

let uu____5933 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____5933))
end
| uu____5934 -> begin
()
end));
(

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let uu___107_5938 = env
in {FStar_TypeChecker_Env.solver = uu___107_5938.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___107_5938.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___107_5938.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___107_5938.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___107_5938.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___107_5938.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___107_5938.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___107_5938.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___107_5938.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___107_5938.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___107_5938.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___107_5938.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___107_5938.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___107_5938.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___107_5938.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___107_5938.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___107_5938.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___107_5938.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___107_5938.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___107_5938.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___107_5938.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___107_5938.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___107_5938.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____5940 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5940) with
| true -> begin
(

let uu____5941 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____5942 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5943 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____5941 uu____5942 uu____5943))))
end
| uu____5944 -> begin
()
end));
(

let uu____5945 = (tc_term env e)
in (match (uu____5945) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in (

let uu____5961 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____5961) with
| true -> begin
(

let subst = (

let uu____5966 = (FStar_List.hd bs)
in (maybe_extend_subst subst uu____5966 e))
in (tc_args head_info ((subst), ((((arg), (None), (FStar_Util.Inl (((c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ))))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____6021 -> begin
(

let uu____6022 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name)
in (match (uu____6022) with
| true -> begin
(

let subst = (

let uu____6027 = (FStar_List.hd bs)
in (maybe_extend_subst subst uu____6027 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____6072 -> begin
(

let uu____6073 = (

let uu____6074 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder uu____6074))
in (match (uu____6073) with
| true -> begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (

let uu____6083 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6083))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end
| uu____6120 -> begin
(

let uu____6121 = (

let uu____6143 = (

let uu____6145 = (

let uu____6146 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____6146))
in (uu____6145)::arg_rets)
in ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), (uu____6143), (g), ((x)::fvs)))
in (tc_args head_info uu____6121 rest rest'))
end))
end))
end))))
end));
))));
)));
)
end
| (uu____6183, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____6204) -> begin
(

let uu____6234 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (uu____6234) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (

let uu____6257 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____6257 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let uu____6273 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (uu____6273) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in ((

let uu____6287 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6287) with
| true -> begin
(

let uu____6288 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" uu____6288))
end
| uu____6289 -> begin
()
end));
(tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args);
))
end))
end
| uu____6318 when (not (norm)) -> begin
(

let uu____6319 = (unfold_whnf env tres)
in (aux true uu____6319))
end
| uu____6320 -> begin
(

let uu____6321 = (

let uu____6322 = (

let uu____6325 = (

let uu____6326 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____6327 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" uu____6326 uu____6327)))
in (

let uu____6331 = (FStar_Syntax_Syntax.argpos arg)
in ((uu____6325), (uu____6331))))
in FStar_Errors.Error (uu____6322))
in (Prims.raise uu____6321))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (

let uu____6347 = (

let uu____6348 = (FStar_Syntax_Util.unrefine tf)
in uu____6348.FStar_Syntax_Syntax.n)
in (match (uu____6347) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let uu____6424 = (tc_term env e)
in (match (uu____6424) with
| (e, c, g_e) -> begin
(

let uu____6437 = (tc_args env tl)
in (match (uu____6437) with
| (args, comps, g_rest) -> begin
(

let uu____6459 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____6459)))
end))
end))
end))
in (

let uu____6470 = (tc_args env args)
in (match (uu____6470) with
| (args, comps, g_args) -> begin
(

let bs = (

let uu____6492 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____6512 -> (match (uu____6512) with
| (uu____6520, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____6492))
in (

let ml_or_tot = (fun t r -> (

let uu____6536 = (FStar_Options.ml_ish ())
in (match (uu____6536) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r)
end
| uu____6537 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____6539 = (

let uu____6542 = (

let uu____6543 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6543 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____6542))
in (ml_or_tot uu____6539 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____6552 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6552) with
| true -> begin
(

let uu____6553 = (FStar_Syntax_Print.term_to_string head)
in (

let uu____6554 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____6555 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____6553 uu____6554 uu____6555))))
end
| uu____6556 -> begin
()
end));
(

let uu____6558 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____6558));
(

let comp = (

let uu____6560 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____6565 out -> (match (uu____6565) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____6560))
in (

let uu____6574 = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let uu____6581 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____6574), (comp), (uu____6581)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6596 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6596) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| uu____6639 -> begin
(match ((not (norm))) with
| true -> begin
(

let uu____6645 = (unfold_whnf env tf)
in (check_function_app true uu____6645))
end
| uu____6646 -> begin
(

let uu____6647 = (

let uu____6648 = (

let uu____6651 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((uu____6651), (head.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____6648))
in (Prims.raise uu____6647))
end)
end)))
in (

let uu____6657 = (

let uu____6658 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____6658))
in (check_function_app false uu____6657)))));
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

let uu____6704 = (FStar_List.fold_left2 (fun uu____6717 uu____6718 uu____6719 -> (match (((uu____6717), (uu____6718), (uu____6719))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((aq <> aq')) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____6762 -> begin
()
end);
(

let uu____6763 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____6763) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (

let uu____6775 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____6775 g))
in (

let ghost = (ghost || ((

let uu____6777 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____6777))) && (

let uu____6778 = (FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)
in (not (uu____6778)))))
in (

let uu____6779 = (

let uu____6785 = (

let uu____6791 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6791)::[])
in (FStar_List.append seen uu____6785))
in (

let uu____6796 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((uu____6779), (uu____6796), (ghost)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____6704) with
| (args, guard, ghost) -> begin
(

let e = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = (match (ghost) with
| true -> begin
(

let uu____6825 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____6825 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____6826 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____6827 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (uu____6827) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| uu____6839 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let uu____6861 = (FStar_Syntax_Subst.open_branch branch)
in (match (uu____6861) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____6887 = branch
in (match (uu____6887) with
| (cpat, uu____6907, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let uu____6949 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (uu____6949) with
| (pat_bvs, exps, p) -> begin
((

let uu____6971 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6971) with
| true -> begin
(

let uu____6972 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____6973 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____6972 uu____6973)))
end
| uu____6974 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let uu____6976 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____6976) with
| (env1, uu____6989) -> begin
(

let env1 = (

let uu___108_6993 = env1
in {FStar_TypeChecker_Env.solver = uu___108_6993.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___108_6993.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___108_6993.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___108_6993.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___108_6993.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___108_6993.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___108_6993.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___108_6993.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___108_6993.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___108_6993.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___108_6993.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___108_6993.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___108_6993.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___108_6993.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___108_6993.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___108_6993.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___108_6993.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___108_6993.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___108_6993.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___108_6993.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___108_6993.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___108_6993.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___108_6993.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let uu____6995 = (

let uu____7000 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> ((

let uu____7012 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7012) with
| true -> begin
(

let uu____7013 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7014 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____7013 uu____7014)))
end
| uu____7015 -> begin
()
end));
(

let uu____7016 = (tc_term env1 e)
in (match (uu____7016) with
| (e, lc, g) -> begin
((

let uu____7026 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7026) with
| true -> begin
(

let uu____7027 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____7028 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" uu____7027 uu____7028)))
end
| uu____7029 -> begin
()
end));
(

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let uu____7032 = (

let uu____7033 = (FStar_TypeChecker_Rel.discharge_guard env (

let uu___109_7034 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___109_7034.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___109_7034.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___109_7034.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right uu____7033 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (

let uu____7048 = (

let uu____7050 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right uu____7050 (FStar_List.map (fun uu____7074 -> (match (uu____7074) with
| (u, uu____7079) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right uu____7048 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____7092 = (

let uu____7093 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____7093))
in (match (uu____7092) with
| true -> begin
(

let unresolved = (

let uu____7100 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right uu____7100 FStar_Util.set_elements))
in (

let uu____7114 = (

let uu____7115 = (

let uu____7118 = (

let uu____7119 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (

let uu____7120 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____7121 = (

let uu____7122 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____7134 -> (match (uu____7134) with
| (u, uu____7142) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____7122 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____7119 uu____7120 uu____7121))))
in ((uu____7118), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____7115))
in (Prims.raise uu____7114)))
end
| uu____7155 -> begin
()
end));
(

let uu____7157 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7157) with
| true -> begin
(

let uu____7158 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____7158))
end
| uu____7159 -> begin
()
end));
((e), (e'));
))))))));
)
end));
))))
in (FStar_All.pipe_right uu____7000 FStar_List.unzip))
in (match (uu____6995) with
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

let uu____7189 = (

let uu____7193 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____7193 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____7189) with
| (scrutinee_env, uu____7206) -> begin
(

let uu____7209 = (tc_pat true pat_t pattern)
in (match (uu____7209) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let uu____7237 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
(

let uu____7252 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____7252) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7259 -> begin
(

let uu____7260 = (

let uu____7264 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term uu____7264 e))
in (match (uu____7260) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end))
end)
in (match (uu____7237) with
| (when_clause, g_when) -> begin
(

let uu____7284 = (tc_term pat_env branch_exp)
in (match (uu____7284) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____7309 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____7309))
end)
in (

let uu____7319 = (

let eqs = (

let uu____7327 = (

let uu____7328 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7328)))
in (match (uu____7327) with
| true -> begin
None
end
| uu____7334 -> begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| uu____7354 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(

let uu____7374 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____7374))
end))
end))) None))
end))
in (

let uu____7386 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (uu____7386) with
| (c, g_branch) -> begin
(

let uu____7396 = (match (((eqs), (when_condition))) with
| uu____7407 when (

let uu____7416 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7416))) -> begin
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

let uu____7442 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (

let uu____7443 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____7442), (uu____7443))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____7462 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____7462))
in (

let uu____7463 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (

let uu____7464 = (

let uu____7465 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____7465 g_when))
in ((uu____7463), (uu____7464))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____7481 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((uu____7481), (g_when)))))
end)
in (match (uu____7396) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (

let uu____7489 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (

let uu____7490 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((uu____7489), (uu____7490), (g_branch)))))
end))
end)))
in (match (uu____7319) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let uu____7503 = (

let uu____7504 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7504)))
in (match (uu____7503) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____7505 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> (

let uu____7537 = (

let uu____7538 = (

let uu____7539 = (

let uu____7541 = (

let uu____7545 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____7545))
in (Prims.snd uu____7541))
in (FStar_List.length uu____7539))
in (uu____7538 > (Prims.parse_int "1")))
in (match (uu____7537) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____7556 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____7556) with
| None -> begin
[]
end
| uu____7567 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational None)
in (

let disc = (

let uu____7575 = (

let uu____7576 = (

let uu____7577 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (uu____7577)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____7576))
in (uu____7575 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (

let uu____7582 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (uu____7582)::[])))
end)))
end
| uu____7589 -> begin
[]
end)))
in (

let fail = (fun uu____7598 -> (

let uu____7599 = (

let uu____7600 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (

let uu____7601 = (FStar_Syntax_Print.term_to_string pat_exp)
in (

let uu____7602 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____7600 uu____7601 uu____7602))))
in (failwith uu____7599)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____7623) -> begin
(head_constructor t)
end
| uu____7629 -> begin
(fail ())
end))
in (

let pat_exp = (

let uu____7632 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right uu____7632 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____7648) -> begin
(

let uu____7649 = (

let uu____7652 = (

let uu____7653 = (

let uu____7654 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (

let uu____7655 = (

let uu____7657 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (uu____7657)::[])
in (uu____7654)::uu____7655))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq uu____7653))
in (uu____7652 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (uu____7649)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in (

let uu____7673 = (

let uu____7674 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____7674)))
in (match (uu____7673) with
| true -> begin
[]
end
| uu____7680 -> begin
(

let uu____7681 = (head_constructor pat_exp)
in (discriminate scrutinee_tm uu____7681))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in (

let uu____7708 = (

let uu____7709 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____7709)))
in (match (uu____7708) with
| true -> begin
[]
end
| uu____7715 -> begin
(

let sub_term_guards = (

let uu____7718 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____7734 -> (match (uu____7734) with
| (ei, uu____7741) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____7751 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____7751) with
| None -> begin
[]
end
| uu____7758 -> begin
(

let sub_term = (

let uu____7765 = (

let uu____7766 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (

let uu____7771 = (

let uu____7772 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (uu____7772)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____7766 uu____7771)))
in (uu____7765 None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____7718 FStar_List.flatten))
in (

let uu____7784 = (discriminate scrutinee_tm f)
in (FStar_List.append uu____7784 sub_term_guards)))
end)))
end
| uu____7792 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> (

let uu____7804 = (

let uu____7805 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7805)))
in (match (uu____7804) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end
| uu____7806 -> begin
(

let t = (

let uu____7808 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____7808))
in (

let uu____7811 = (FStar_Syntax_Util.type_u ())
in (match (uu____7811) with
| (k, uu____7815) -> begin
(

let uu____7816 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____7816) with
| (t, uu____7821, uu____7822) -> begin
t
end))
end)))
end)))
in (

let branch_guard = (

let uu____7824 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right uu____7824 FStar_Syntax_Util.mk_disj_l))
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

let uu____7841 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7841) with
| true -> begin
(

let uu____7842 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____7842))
end
| uu____7843 -> begin
()
end));
(

let uu____7844 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((uu____7844), (branch_guard), (c), (guard)));
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

let uu____7862 = (check_let_bound_def true env lb)
in (match (uu____7862) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let uu____7876 = (match ((annotated && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
((g1), (e1), (univ_vars), (c1))
end
| uu____7885 -> begin
(

let g1 = (

let uu____7887 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right uu____7887 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____7889 = (

let uu____7894 = (

let uu____7900 = (

let uu____7905 = (

let uu____7913 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____7913)))
in (uu____7905)::[])
in (FStar_TypeChecker_Util.generalize env uu____7900))
in (FStar_List.hd uu____7894))
in (match (uu____7889) with
| (uu____7942, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end)
in (match (uu____7876) with
| (g1, e1, univ_vars, c1) -> begin
(

let uu____7953 = (

let uu____7958 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____7958) with
| true -> begin
(

let uu____7963 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (uu____7963) with
| (ok, c1) -> begin
(match (ok) with
| true -> begin
((e2), (c1))
end
| uu____7978 -> begin
((

let uu____7980 = (FStar_Options.warn_top_level_effects ())
in (match (uu____7980) with
| true -> begin
(

let uu____7981 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.warn uu____7981 FStar_TypeChecker_Err.top_level_effect))
end
| uu____7982 -> begin
()
end));
(

let uu____7983 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))))) None e2.FStar_Syntax_Syntax.pos)
in ((uu____7983), (c1)));
)
end)
end))
end
| uu____7998 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let c = (

let uu____8001 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right uu____8001 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c)));
)
end))
in (match (uu____7953) with
| (e2, c1) -> begin
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env (FStar_Syntax_Util.comp_effect_name c1) FStar_Syntax_Syntax.U_zero FStar_TypeChecker_Common.t_unit)
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (

let uu____8024 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((uu____8024), ((FStar_Syntax_Util.lcomp_of_comp cres)), (FStar_TypeChecker_Rel.trivial_guard))));
))
end))
end))
end))
end
| uu____8043 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let uu___110_8064 = env
in {FStar_TypeChecker_Env.solver = uu___110_8064.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___110_8064.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___110_8064.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___110_8064.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___110_8064.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___110_8064.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___110_8064.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___110_8064.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___110_8064.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___110_8064.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___110_8064.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___110_8064.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___110_8064.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___110_8064.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___110_8064.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___110_8064.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___110_8064.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___110_8064.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___110_8064.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___110_8064.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___110_8064.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___110_8064.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___110_8064.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____8065 = (

let uu____8071 = (

let uu____8072 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____8072 Prims.fst))
in (check_let_bound_def false uu____8071 lb))
in (match (uu____8065) with
| (e1, uu____8084, c1, g1, annotated) -> begin
(

let x = (

let uu___111_8089 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___111_8089.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___111_8089.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____8090 = (

let uu____8093 = (

let uu____8094 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____8094)::[])
in (FStar_Syntax_Subst.open_term uu____8093 e2))
in (match (uu____8090) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let uu____8106 = (

let uu____8110 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term uu____8110 e2))
in (match (uu____8106) with
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

let uu____8125 = (

let uu____8128 = (

let uu____8129 = (

let uu____8137 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (uu____8137)))
in FStar_Syntax_Syntax.Tm_let (uu____8129))
in (FStar_Syntax_Syntax.mk uu____8128))
in (uu____8125 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____8152 = (

let uu____8153 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ uu____8153 e1))
in (FStar_All.pipe_left (fun _0_32 -> FStar_TypeChecker_Common.NonTrivial (_0_32)) uu____8152))
in (

let g2 = (

let uu____8159 = (

let uu____8160 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____8160 g2))
in (FStar_TypeChecker_Rel.close_guard xb uu____8159))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (

let uu____8162 = (

let uu____8163 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome uu____8163))
in (match (uu____8162) with
| true -> begin
(

let tt = (

let uu____8169 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right uu____8169 FStar_Option.get))
in ((

let uu____8173 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____8173) with
| true -> begin
(

let uu____8174 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____8175 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____8174 uu____8175)))
end
| uu____8176 -> begin
()
end));
((e), (cres), (guard));
))
end
| uu____8177 -> begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____8180 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____8180) with
| true -> begin
(

let uu____8181 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____8182 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____8181 uu____8182)))
end
| uu____8183 -> begin
()
end));
((e), ((

let uu___112_8184 = cres
in {FStar_Syntax_Syntax.eff_name = uu___112_8184.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___112_8184.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___112_8184.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____8185 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8206 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8206) with
| (lbs, e2) -> begin
(

let uu____8217 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8217) with
| (env0, topt) -> begin
(

let uu____8228 = (build_let_rec_env true env0 lbs)
in (match (uu____8228) with
| (lbs, rec_env) -> begin
(

let uu____8239 = (check_let_recs rec_env lbs)
in (match (uu____8239) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (

let uu____8251 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right uu____8251 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (

let uu____8255 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____8255 (fun _0_33 -> Some (_0_33))))
in (

let lbs = (match ((not (env.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (match ((lb.FStar_Syntax_Syntax.lbunivs = [])) with
| true -> begin
lb
end
| uu____8271 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end))))
end
| uu____8272 -> begin
(

let ecs = (

let uu____8279 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____8301 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____8301))))))
in (FStar_TypeChecker_Util.generalize env uu____8279))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____8321 -> (match (uu____8321) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (

let uu____8346 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8346))
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let uu____8355 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____8355) with
| (lbs, e2) -> begin
(

let uu____8366 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____8381 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((uu____8366), (cres), (uu____8381))))
end));
)))))
end))
end))
end))
end))
end
| uu____8384 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8405 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8405) with
| (lbs, e2) -> begin
(

let uu____8416 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8416) with
| (env0, topt) -> begin
(

let uu____8427 = (build_let_rec_env false env0 lbs)
in (match (uu____8427) with
| (lbs, rec_env) -> begin
(

let uu____8438 = (check_let_recs rec_env lbs)
in (match (uu____8438) with
| (lbs, g_lbs) -> begin
(

let uu____8449 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let uu___113_8460 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___113_8460.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___113_8460.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let uu___114_8462 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___114_8462.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___114_8462.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___114_8462.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___114_8462.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (uu____8449) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____8479 = (tc_term env e2)
in (match (uu____8479) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___115_8493 = cres
in {FStar_Syntax_Syntax.eff_name = uu___115_8493.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___115_8493.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___115_8493.FStar_Syntax_Syntax.comp})
in (

let uu____8494 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____8494) with
| (lbs, e2) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (uu____8523) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let uu___116_8528 = cres
in {FStar_Syntax_Syntax.eff_name = uu___116_8528.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___116_8528.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___116_8528.FStar_Syntax_Syntax.comp})
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
| uu____8531 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let uu____8547 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____8547) with
| (uu____8553, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let uu____8564 = (FStar_List.fold_left (fun uu____8571 lb -> (match (uu____8571) with
| (lbs, env) -> begin
(

let uu____8583 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (uu____8583) with
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
| uu____8596 -> begin
(

let uu____8597 = (

let uu____8601 = (

let uu____8602 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst uu____8602))
in (tc_check_tot_or_gtot_term (

let uu___117_8607 = env0
in {FStar_TypeChecker_Env.solver = uu___117_8607.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_8607.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_8607.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_8607.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_8607.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_8607.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_8607.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_8607.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_8607.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_8607.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_8607.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_8607.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_8607.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___117_8607.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___117_8607.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___117_8607.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_8607.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___117_8607.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___117_8607.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___117_8607.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_8607.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___117_8607.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___117_8607.FStar_TypeChecker_Env.qname_and_index}) t uu____8601))
in (match (uu____8597) with
| (t, uu____8609, g) -> begin
(

let g = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((

let uu____8613 = (FStar_TypeChecker_Rel.discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore uu____8613));
(norm env0 t);
))
end))
end)
in (

let env = (

let uu____8615 = ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env))
in (match (uu____8615) with
| true -> begin
(

let uu___118_8616 = env
in {FStar_TypeChecker_Env.solver = uu___118_8616.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___118_8616.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___118_8616.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___118_8616.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___118_8616.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___118_8616.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___118_8616.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___118_8616.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___118_8616.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___118_8616.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___118_8616.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___118_8616.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___118_8616.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___118_8616.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___118_8616.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___118_8616.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___118_8616.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___118_8616.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___118_8616.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___118_8616.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___118_8616.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___118_8616.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___118_8616.FStar_TypeChecker_Env.qname_and_index})
end
| uu____8623 -> begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end))
in (

let lb = (

let uu___119_8626 = lb
in {FStar_Syntax_Syntax.lbname = uu___119_8626.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___119_8626.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____8564) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____8640 = (

let uu____8645 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____8656 = (

let uu____8660 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____8660 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____8656) with
| (e, c, g) -> begin
((

let uu____8667 = (

let uu____8668 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____8668)))
in (match (uu____8667) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____8669 -> begin
()
end));
(

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g)));
)
end)))))
in (FStar_All.pipe_right uu____8645 FStar_List.unzip))
in (match (uu____8640) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____8697 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8697) with
| (env1, uu____8707) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____8713 = (check_lbtyp top_level env lb)
in (match (uu____8713) with
| (topt, wf_annot, univ_vars, univ_opening, env1) -> begin
((match (((not (top_level)) && (univ_vars <> []))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____8736 -> begin
()
end);
(

let e1 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____8739 = (tc_maybe_toplevel_term (

let uu___120_8743 = env1
in {FStar_TypeChecker_Env.solver = uu___120_8743.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___120_8743.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___120_8743.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___120_8743.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___120_8743.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___120_8743.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___120_8743.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___120_8743.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___120_8743.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___120_8743.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___120_8743.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___120_8743.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___120_8743.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___120_8743.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___120_8743.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___120_8743.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___120_8743.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___120_8743.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___120_8743.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___120_8743.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___120_8743.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___120_8743.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___120_8743.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (uu____8739) with
| (e1, c1, g1) -> begin
(

let uu____8752 = (

let uu____8755 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____8758 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____8755 e1 c1 wf_annot))
in (match (uu____8752) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____8768 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____8768) with
| true -> begin
(

let uu____8769 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____8770 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____8771 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" uu____8769 uu____8770 uu____8771))))
end
| uu____8772 -> begin
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
| uu____8793 -> begin
()
end);
((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____8797 -> begin
(

let uu____8798 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____8798) with
| (univ_opening, univ_vars) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____8825 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (univ_opening), (uu____8825)))
end
| uu____8829 -> begin
(

let uu____8830 = (FStar_Syntax_Util.type_u ())
in (match (uu____8830) with
| (k, uu____8841) -> begin
(

let uu____8842 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____8842) with
| (t, uu____8854, g) -> begin
((

let uu____8857 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8857) with
| true -> begin
(

let uu____8858 = (

let uu____8859 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____8859))
in (

let uu____8860 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____8858 uu____8860)))
end
| uu____8861 -> begin
()
end));
(

let t = (norm env1 t)
in (

let uu____8863 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (univ_opening), (uu____8863))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____8868 -> (match (uu____8868) with
| (x, imp) -> begin
(

let uu____8879 = (FStar_Syntax_Util.type_u ())
in (match (uu____8879) with
| (tu, u) -> begin
((

let uu____8891 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____8891) with
| true -> begin
(

let uu____8892 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____8893 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____8894 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____8892 uu____8893 uu____8894))))
end
| uu____8895 -> begin
()
end));
(

let uu____8896 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____8896) with
| (t, uu____8907, g) -> begin
(

let x = (((

let uu___121_8912 = x
in {FStar_Syntax_Syntax.ppname = uu___121_8912.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_8912.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____8914 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8914) with
| true -> begin
(

let uu____8915 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (

let uu____8916 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____8915 uu____8916)))
end
| uu____8917 -> begin
()
end));
(

let uu____8918 = (push_binding env x)
in ((x), (uu____8918), (g), (u)));
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

let uu____8969 = (tc_binder env b)
in (match (uu____8969) with
| (b, env', g, u) -> begin
(

let uu____8992 = (aux env' bs)
in (match (uu____8992) with
| (bs, env', g', us) -> begin
(

let uu____9021 = (

let uu____9022 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____9022))
in (((b)::bs), (env'), (uu____9021), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun uu____9065 uu____9066 -> (match (((uu____9065), (uu____9066))) with
| ((t, imp), (args, g)) -> begin
(

let uu____9103 = (tc_term env t)
in (match (uu____9103) with
| (t, uu____9113, g') -> begin
(

let uu____9115 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (uu____9115)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____9133 -> (match (uu____9133) with
| (pats, g) -> begin
(

let uu____9147 = (tc_args env p)
in (match (uu____9147) with
| (args, g') -> begin
(

let uu____9155 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (uu____9155)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____9163 = (tc_maybe_toplevel_term env e)
in (match (uu____9163) with
| (e, c, g) -> begin
(

let uu____9173 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____9173) with
| true -> begin
((e), (c), (g))
end
| uu____9177 -> begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let c = (norm_c env c)
in (

let uu____9183 = (

let uu____9186 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c))
in (match (uu____9186) with
| true -> begin
(

let uu____9189 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((uu____9189), (false)))
end
| uu____9190 -> begin
(

let uu____9191 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((uu____9191), (true)))
end))
in (match (uu____9183) with
| (target_comp, allow_ghost) -> begin
(

let uu____9197 = (FStar_TypeChecker_Rel.sub_comp env c target_comp)
in (match (uu____9197) with
| Some (g') -> begin
(

let uu____9203 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (uu____9203)))
end
| uu____9204 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____9209 = (

let uu____9210 = (

let uu____9213 = (FStar_TypeChecker_Err.expected_ghost_expression e c)
in ((uu____9213), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____9210))
in (Prims.raise uu____9209))
end
| uu____9217 -> begin
(

let uu____9218 = (

let uu____9219 = (

let uu____9222 = (FStar_TypeChecker_Err.expected_pure_expression e c)
in ((uu____9222), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____9219))
in (Prims.raise uu____9218))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____9235 = (tc_tot_or_gtot_term env t)
in (match (uu____9235) with
| (t, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____9255 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____9255) with
| true -> begin
(

let uu____9256 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____9256))
end
| uu____9257 -> begin
()
end));
(

let env = (

let uu___122_9259 = env
in {FStar_TypeChecker_Env.solver = uu___122_9259.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___122_9259.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___122_9259.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___122_9259.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___122_9259.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___122_9259.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___122_9259.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___122_9259.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___122_9259.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___122_9259.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___122_9259.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___122_9259.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___122_9259.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___122_9259.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___122_9259.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___122_9259.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___122_9259.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___122_9259.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___122_9259.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___122_9259.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___122_9259.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___122_9259.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___122_9259.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____9260 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Errors.Error (msg, uu____9276) -> begin
(

let uu____9277 = (

let uu____9278 = (

let uu____9281 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (uu____9281)))
in FStar_Errors.Error (uu____9278))
in (Prims.raise uu____9277))
end
in (match (uu____9260) with
| (t, c, g) -> begin
(

let uu____9291 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____9291) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____9297 -> begin
(

let uu____9298 = (

let uu____9299 = (

let uu____9302 = (

let uu____9303 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____9303))
in (

let uu____9304 = (FStar_TypeChecker_Env.get_range env)
in ((uu____9302), (uu____9304))))
in FStar_Errors.Error (uu____9299))
in (Prims.raise uu____9298))
end))
end)));
))


let level_of_type_fail = (fun env e t -> (

let uu____9325 = (

let uu____9326 = (

let uu____9329 = (

let uu____9330 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____9330 t))
in (

let uu____9331 = (FStar_TypeChecker_Env.get_range env)
in ((uu____9329), (uu____9331))))
in FStar_Errors.Error (uu____9326))
in (Prims.raise uu____9325)))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t -> (

let uu____9348 = (

let uu____9349 = (FStar_Syntax_Util.unrefine t)
in uu____9349.FStar_Syntax_Syntax.n)
in (match (uu____9348) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____9353 -> begin
(match (retry) with
| true -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (aux false t))
end
| uu____9355 -> begin
(

let uu____9356 = (FStar_Syntax_Util.type_u ())
in (match (uu____9356) with
| (t_u, u) -> begin
(

let env = (

let uu___125_9362 = env
in {FStar_TypeChecker_Env.solver = uu___125_9362.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___125_9362.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___125_9362.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___125_9362.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___125_9362.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___125_9362.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___125_9362.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___125_9362.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___125_9362.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___125_9362.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___125_9362.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___125_9362.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___125_9362.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___125_9362.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___125_9362.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___125_9362.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___125_9362.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___125_9362.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___125_9362.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___125_9362.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___125_9362.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___125_9362.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___125_9362.FStar_TypeChecker_Env.qname_and_index})
in (

let g = (FStar_TypeChecker_Rel.teq env t t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____9366 = (FStar_Syntax_Print.term_to_string t)
in (level_of_type_fail env e uu____9366))
end
| uu____9367 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____9376 = (

let uu____9377 = (FStar_Syntax_Subst.compress e)
in uu____9377.FStar_Syntax_Syntax.n)
in (match (uu____9376) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____9386) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____9397) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____9422, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____9437) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n) -> begin
n.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____9444 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9444) with
| (uu____9453, t) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____9455, FStar_Util.Inl (t), uu____9457) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____9476, FStar_Util.Inr (c), uu____9478) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u)))) None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____9508; FStar_Syntax_Syntax.pos = uu____9509; FStar_Syntax_Syntax.vars = uu____9510}, us) -> begin
(

let uu____9516 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9516) with
| (us', t) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____9532 = (

let uu____9533 = (

let uu____9536 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____9536)))
in FStar_Errors.Error (uu____9533))
in (Prims.raise uu____9532))
end
| uu____9537 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____9544 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____9545) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____9553) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____9570 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____9570) with
| (bs, c) -> begin
(

let us = (FStar_List.map (fun uu____9581 -> (match (uu____9581) with
| (b, uu____9585) -> begin
(

let uu____9586 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____9586))
end)) bs)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c)
in (

let uu____9591 = (universe_of_aux env res)
in (level_of_type env res uu____9591)))
in (

let u_c = (

let uu____9593 = (FStar_TypeChecker_Util.effect_repr env c u_res)
in (match (uu____9593) with
| None -> begin
u_res
end
| Some (trepr) -> begin
(

let uu____9596 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____9596))
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

let uu____9682 = (universe_of_aux env hd)
in ((uu____9682), (args)))
end
| FStar_Syntax_Syntax.Tm_match (uu____9692, (hd)::uu____9694) -> begin
(

let uu____9741 = (FStar_Syntax_Subst.open_branch hd)
in (match (uu____9741) with
| (uu____9751, uu____9752, hd) -> begin
(

let uu____9768 = (FStar_Syntax_Util.head_and_args hd)
in (match (uu____9768) with
| (hd, args) -> begin
(type_of_head retry hd args)
end))
end))
end
| uu____9803 when retry -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____9805 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____9805) with
| (hd, args) -> begin
(type_of_head false hd args)
end)))
end
| uu____9840 -> begin
(

let uu____9841 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9841) with
| (env, uu____9855) -> begin
(

let env = (

let uu___126_9859 = env
in {FStar_TypeChecker_Env.solver = uu___126_9859.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___126_9859.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___126_9859.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___126_9859.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___126_9859.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___126_9859.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___126_9859.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___126_9859.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___126_9859.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___126_9859.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___126_9859.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___126_9859.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___126_9859.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___126_9859.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___126_9859.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___126_9859.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___126_9859.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___126_9859.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___126_9859.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___126_9859.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___126_9859.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____9861 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("UniverseOf")))
in (match (uu____9861) with
| true -> begin
(

let uu____9862 = (

let uu____9863 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____9863))
in (

let uu____9864 = (FStar_Syntax_Print.term_to_string hd)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____9862 uu____9864)))
end
| uu____9865 -> begin
()
end));
(

let uu____9866 = (tc_term env hd)
in (match (uu____9866) with
| (uu____9879, {FStar_Syntax_Syntax.eff_name = uu____9880; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____9882; FStar_Syntax_Syntax.comp = uu____9883}, g) -> begin
((

let uu____9893 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____9893 Prims.ignore));
((t), (args));
)
end));
))
end))
end)))
in (

let uu____9901 = (type_of_head true hd args)
in (match (uu____9901) with
| (t, args) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____9930 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____9930) with
| (bs, res) -> begin
(

let res = (FStar_Syntax_Util.comp_result res)
in (match (((FStar_List.length bs) = (FStar_List.length args))) with
| true -> begin
(

let subst = (FStar_Syntax_Util.subst_of_list bs args)
in (FStar_Syntax_Subst.subst subst res))
end
| uu____9962 -> begin
(

let uu____9963 = (FStar_Syntax_Print.term_to_string res)
in (level_of_type_fail env e uu____9963))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____9966, (hd)::uu____9968) -> begin
(

let uu____10015 = (FStar_Syntax_Subst.open_branch hd)
in (match (uu____10015) with
| (uu____10018, uu____10019, hd) -> begin
(universe_of_aux env hd)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____10035, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____10069 = (universe_of_aux env e)
in (level_of_type env e uu____10069)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____10082 = (tc_binders env tps)
in (match (uu____10082) with
| (tps, env, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((tps), (env), (us));
)
end)))




