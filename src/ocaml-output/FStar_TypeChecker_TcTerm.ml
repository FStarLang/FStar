
open Prims

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___94_4 = env
in {FStar_TypeChecker_Env.solver = uu___94_4.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___94_4.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___94_4.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___94_4.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___94_4.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___94_4.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___94_4.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___94_4.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___94_4.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___94_4.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___94_4.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___94_4.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___94_4.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___94_4.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___94_4.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___94_4.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___94_4.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___94_4.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___94_4.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___94_4.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___94_4.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___94_4.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___94_4.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___95_8 = env
in {FStar_TypeChecker_Env.solver = uu___95_8.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___95_8.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___95_8.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___95_8.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___95_8.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___95_8.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___95_8.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___95_8.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___95_8.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___95_8.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___95_8.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___95_8.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___95_8.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___95_8.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___95_8.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___95_8.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___95_8.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___95_8.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___95_8.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___95_8.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___95_8.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___95_8.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___95_8.FStar_TypeChecker_Env.qname_and_index}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = (match ((tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
| true -> begin
v.FStar_Syntax_Syntax.pos
end
| uu____33 -> begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end)
in ((let _0_314 = (let _0_313 = (FStar_Syntax_Syntax.as_arg v)
in (let _0_312 = (let _0_311 = (FStar_Syntax_Syntax.as_arg tl)
in (_0_311)::[])
in (_0_313)::_0_312))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _0_314)) (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun uu___89_41 -> (match (uu___89_41) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____43 -> begin
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
| uu____94 -> begin
(

let t = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____97 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t)
in (

let uu____100 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____100) with
| None -> begin
t
end
| Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t)
end
| uu____104 -> begin
(

let fail = (fun uu____108 -> (

let msg = (match (head_opt) with
| None -> begin
(let _0_315 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _0_315))
end
| Some (head) -> begin
(let _0_317 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_316 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _0_317 _0_316)))
end)
in (Prims.raise (FStar_Errors.Error ((let _0_318 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_0_318))))))))
in (

let s = (let _0_320 = (let _0_319 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _0_319))
in (FStar_TypeChecker_Util.new_uvar env _0_320))
in (

let uu____114 = (FStar_TypeChecker_Rel.try_teq env t s)
in (match (uu____114) with
| Some (g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
s;
)
end
| uu____118 -> begin
(fail ())
end))))
end)
end))))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> (

let uu____149 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____149) with
| true -> begin
s
end
| uu____150 -> begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let uu___96_163 = lc
in {FStar_Syntax_Syntax.eff_name = uu___96_163.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___96_163.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____164 -> (let _0_321 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _0_321 t)))}))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> ((FStar_ST.write e.FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)));
e;
))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (

let uu____201 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____201) with
| FStar_Syntax_Syntax.Tm_arrow (uu____202, c) -> begin
(

let uu____214 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c))
in (match (uu____214) with
| true -> begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (

let uu____216 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____216) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____218) -> begin
false
end
| uu____219 -> begin
true
end)))
end
| uu____220 -> begin
false
end))
end
| uu____221 -> begin
true
end)))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(FStar_Syntax_Util.lcomp_of_comp (

let uu____224 = ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env))))
in (match (uu____224) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____227 -> begin
(FStar_TypeChecker_Util.return_value env t e)
end)))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____232 = (

let uu____236 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____236) with
| None -> begin
(let _0_322 = (memo_tk e t)
in ((_0_322), (lc), (guard)))
end
| Some (t') -> begin
((

let uu____243 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____243) with
| true -> begin
(let _0_324 = (FStar_Syntax_Print.term_to_string t)
in (let _0_323 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _0_324 _0_323)))
end
| uu____244 -> begin
()
end));
(

let uu____245 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____245) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____256 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (uu____256) with
| (e, g) -> begin
((

let uu____265 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____265) with
| true -> begin
(let _0_328 = (FStar_Syntax_Print.term_to_string t)
in (let _0_327 = (FStar_Syntax_Print.term_to_string t')
in (let _0_326 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (let _0_325 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" _0_328 _0_327 _0_326 _0_325)))))
end
| uu____266 -> begin
()
end));
(

let msg = (

let uu____271 = (FStar_TypeChecker_Rel.is_trivial g)
in (match (uu____271) with
| true -> begin
None
end
| uu____277 -> begin
(FStar_All.pipe_left (fun _0_329 -> Some (_0_329)) (FStar_TypeChecker_Err.subtyping_failed env t t'))
end))
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____286 = (FStar_TypeChecker_Util.strengthen_precondition msg env e lc g)
in (match (uu____286) with
| (lc, g) -> begin
(let _0_330 = (memo_tk e t')
in ((_0_330), ((set_lcomp_result lc t')), (g)))
end))));
)
end)))
end));
)
end))
in (match (uu____232) with
| (e, lc, g) -> begin
((

let uu____301 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____301) with
| true -> begin
(let _0_331 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _0_331))
end
| uu____302 -> begin
()
end));
((e), (lc), (g));
)
end))))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____318 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____318) with
| None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (t) -> begin
(

let uu____324 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____324) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt uu____346 -> (match (uu____346) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (uu____361) -> begin
copt
end
| None -> begin
(

let uu____362 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (not ((FStar_Syntax_Util.is_pure_or_ghost_comp c)))))
in (match (uu____362) with
| true -> begin
Some ((FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos))
end
| uu____364 -> begin
(

let uu____365 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____365) with
| true -> begin
None
end
| uu____367 -> begin
(

let uu____368 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____368) with
| true -> begin
Some ((FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c)))
end
| uu____370 -> begin
(

let uu____371 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____371) with
| true -> begin
Some ((FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c)))
end
| uu____373 -> begin
None
end))
end))
end))
end))
end)
in (match (expected_c_opt) with
| None -> begin
(let _0_332 = (norm_c env c)
in ((e), (_0_332), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
((

let uu____379 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____379) with
| true -> begin
(let _0_335 = (FStar_Syntax_Print.term_to_string e)
in (let _0_334 = (FStar_Syntax_Print.comp_to_string c)
in (let _0_333 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _0_335 _0_334 _0_333))))
end
| uu____380 -> begin
()
end));
(

let c = (norm_c env c)
in ((

let uu____383 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____383) with
| true -> begin
(let _0_338 = (FStar_Syntax_Print.term_to_string e)
in (let _0_337 = (FStar_Syntax_Print.comp_to_string c)
in (let _0_336 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _0_338 _0_337 _0_336))))
end
| uu____384 -> begin
()
end));
(

let uu____385 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (uu____385) with
| (e, uu____393, g) -> begin
(

let g = (let _0_339 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _0_339 "could not prove post-condition" g))
in ((

let uu____397 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____397) with
| true -> begin
(let _0_341 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _0_340 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _0_341 _0_340)))
end
| uu____398 -> begin
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


let no_logical_guard = (fun env uu____419 -> (match (uu____419) with
| (te, kt, f) -> begin
(

let uu____426 = (FStar_TypeChecker_Rel.guard_form f)
in (match (uu____426) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_343 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f)
in (let _0_342 = (FStar_TypeChecker_Env.get_range env)
in ((_0_343), (_0_342)))))))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let uu____437 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____437) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _0_344 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _0_344))
end)))


let check_smt_pat = (fun env t bs c -> (

let uu____474 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____474) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____475; FStar_Syntax_Syntax.effect_name = uu____476; FStar_Syntax_Syntax.result_typ = uu____477; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____481))::[]; FStar_Syntax_Syntax.flags = uu____482}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats))
in (

let uu____516 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____528 -> (match (uu____528) with
| (b, uu____532) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))
in (match (uu____516) with
| None -> begin
()
end
| Some (x, uu____536) -> begin
(let _0_346 = (let _0_345 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _0_345))
in (FStar_Errors.warn t.FStar_Syntax_Syntax.pos _0_346))
end)))
end
| uu____539 -> begin
(failwith "Impossible")
end)
end
| uu____540 -> begin
()
end)))


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (

let uu____560 = (not ((FStar_TypeChecker_Env.should_verify env)))
in (match (uu____560) with
| true -> begin
env.FStar_TypeChecker_Env.letrecs
end
| uu____564 -> begin
(match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env = (

let uu___97_578 = env
in {FStar_TypeChecker_Env.solver = uu___97_578.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___97_578.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___97_578.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___97_578.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___97_578.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___97_578.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___97_578.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___97_578.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___97_578.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___97_578.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___97_578.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___97_578.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___97_578.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___97_578.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___97_578.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___97_578.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___97_578.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___97_578.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___97_578.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___97_578.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___97_578.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___97_578.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___97_578.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu____601 -> (match (uu____601) with
| (b, uu____606) -> begin
(

let t = (let _0_347 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _0_347))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| uu____611 -> begin
(let _0_348 = (FStar_Syntax_Syntax.bv_to_name b)
in (_0_348)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____616 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____616) with
| (head, uu____627) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| uu____643 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____646 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___90_650 -> (match (uu___90_650) with
| FStar_Syntax_Syntax.DECREASES (uu____651) -> begin
true
end
| uu____654 -> begin
false
end))))
in (match (uu____646) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____658 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____664 -> begin
(mk_lex_list xs)
end))
end))))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____676 -> (match (uu____676) with
| (l, t) -> begin
(

let uu____685 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____685) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun uu____716 -> (match (uu____716) with
| (x, imp) -> begin
(

let uu____723 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____723) with
| true -> begin
(let _0_350 = (let _0_349 = Some ((FStar_Syntax_Syntax.range_of_bv x))
in (FStar_Syntax_Syntax.new_bv _0_349 x.FStar_Syntax_Syntax.sort))
in ((_0_350), (imp)))
end
| uu____726 -> begin
((x), (imp))
end))
end))))
in (

let uu____727 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____727) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = ((let _0_354 = (let _0_353 = (FStar_Syntax_Syntax.as_arg dec)
in (let _0_352 = (let _0_351 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_0_351)::[])
in (_0_353)::_0_352))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _0_354)) None r)
in (

let uu____744 = (FStar_Util.prefix formals)
in (match (uu____744) with
| (bs, (last, imp)) -> begin
(

let last = (

let uu___98_770 = last
in (let _0_355 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = uu___98_770.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___98_770.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_355}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in ((

let uu____785 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____785) with
| true -> begin
(let _0_358 = (FStar_Syntax_Print.lbname_to_string l)
in (let _0_357 = (FStar_Syntax_Print.term_to_string t)
in (let _0_356 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _0_358 _0_357 _0_356))))
end
| uu____786 -> begin
()
end));
((l), (t'));
))))
end))))
end)))
end
| uu____789 -> begin
(Prims.raise (FStar_Errors.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let uu___99_1053 = env
in {FStar_TypeChecker_Env.solver = uu___99_1053.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___99_1053.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___99_1053.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___99_1053.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___99_1053.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___99_1053.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___99_1053.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___99_1053.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___99_1053.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___99_1053.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___99_1053.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___99_1053.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___99_1053.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___99_1053.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___99_1053.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___99_1053.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___99_1053.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___99_1053.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___99_1053.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___99_1053.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___99_1053.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___99_1053.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___99_1053.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (match ((e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____1060 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____1062 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____1062) with
| true -> begin
(let _0_361 = (let _0_359 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _0_359))
in (let _0_360 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _0_361 _0_360)))
end
| uu____1063 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1068) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____1107 = (tc_tot_or_gtot_term env e)
in (match (uu____1107) with
| (e, c, g) -> begin
(

let g = (

let uu___100_1118 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___100_1118.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___100_1118.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___100_1118.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____1131 = (FStar_Syntax_Util.type_u ())
in (match (uu____1131) with
| (t, u) -> begin
(

let uu____1139 = (tc_check_tot_or_gtot_term env e t)
in (match (uu____1139) with
| (e, c, g) -> begin
(

let uu____1149 = (

let uu____1158 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1158) with
| (env, uu____1171) -> begin
(tc_pats env pats)
end))
in (match (uu____1149) with
| (pats, g') -> begin
(

let g' = (

let uu___101_1192 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___101_1192.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___101_1192.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___101_1192.FStar_TypeChecker_Env.implicits})
in (let _0_363 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats)))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _0_362 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_0_363), (c), (_0_362)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____1212 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____1212) with
| FStar_Syntax_Syntax.Tm_let ((uu____1216, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____1218; FStar_Syntax_Syntax.lbtyp = uu____1219; FStar_Syntax_Syntax.lbeff = uu____1220; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____1238 = (let _0_364 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _0_364 e1))
in (match (uu____1238) with
| (e1, c1, g1) -> begin
(

let uu____1248 = (tc_term env e2)
in (match (uu____1248) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_367 = (let _0_366 = (let _0_365 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_0_365)::[])
in ((false), (_0_366)))
in ((_0_367), (e2)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _0_368 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_0_368))))))
end))
end))
end
| uu____1295 -> begin
(

let uu____1296 = (tc_term env e)
in (match (uu____1296) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____1320)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let uu____1335 = (tc_term env e)
in (match (uu____1335) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), uu____1360) -> begin
(

let uu____1379 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1379) with
| (env0, uu____1387) -> begin
(

let uu____1390 = (tc_comp env0 expected_c)
in (match (uu____1390) with
| (expected_c, uu____1398, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let uu____1403 = (let _0_369 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _0_369 e))
in (match (uu____1403) with
| (e, c', g') -> begin
(

let uu____1413 = (let _0_371 = (let _0_370 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_0_370)))
in (check_expected_effect env0 (Some (expected_c)) _0_371))
in (match (uu____1413) with
| (e, expected_c, g'') -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c))))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (let _0_372 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _0_372))
in (

let uu____1449 = (comp_check_expected_typ env e lc)
in (match (uu____1449) with
| (e, c, f2) -> begin
(let _0_373 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (_0_373)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), uu____1461) -> begin
(

let uu____1480 = (FStar_Syntax_Util.type_u ())
in (match (uu____1480) with
| (k, u) -> begin
(

let uu____1488 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____1488) with
| (t, uu____1496, f) -> begin
(

let uu____1498 = (let _0_374 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _0_374 e))
in (match (uu____1498) with
| (e, c, g) -> begin
(

let uu____1508 = (let _0_375 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____1513 -> FStar_TypeChecker_Err.ill_kinded_type))) _0_375 e c f))
in (match (uu____1508) with
| (c, f) -> begin
(

let uu____1519 = (let _0_376 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name)))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _0_376 c))
in (match (uu____1519) with
| (e, c, f2) -> begin
(let _0_378 = (let _0_377 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _0_377))
in ((e), (c), (_0_378)))
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

let uu____1624 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1624) with
| (unary_op, uu____1638) -> begin
(

let head = (let _0_379 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[]))))) None _0_379))
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest))))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____1699; FStar_Syntax_Syntax.pos = uu____1700; FStar_Syntax_Syntax.vars = uu____1701}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____1726 -> begin
()
end);
(

let uu____1727 = (

let uu____1731 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1731) with
| (env0, uu____1739) -> begin
(tc_term env0 e)
end))
in (match (uu____1727) with
| (e, c, g) -> begin
(

let uu____1748 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1748) with
| (reify_op, uu____1762) -> begin
(

let u_c = (

let uu____1778 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (uu____1778) with
| (uu____1782, c, uu____1784) -> begin
(

let uu____1785 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n
in (match (uu____1785) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____1787 -> begin
(failwith "Unexpected result type of computation")
end))
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[]))))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _0_380 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _0_380 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____1810 = (comp_check_expected_typ env e c)
in (match (uu____1810) with
| (e, c, g') -> begin
(let _0_381 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_0_381)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = uu____1821; FStar_Syntax_Syntax.pos = uu____1822; FStar_Syntax_Syntax.vars = uu____1823}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____1848 -> begin
()
end);
(

let no_reflect = (fun uu____1855 -> (Prims.raise (FStar_Errors.Error ((let _0_382 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_0_382), (e.FStar_Syntax_Syntax.pos)))))))
in (

let uu____1859 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1859) with
| (reflect_op, uu____1873) -> begin
(

let uu____1888 = (FStar_TypeChecker_Env.effect_decl_opt env l)
in (match (uu____1888) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
(

let uu____1894 = (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers FStar_Syntax_Syntax.contains_reflectable)))
in (match (uu____1894) with
| true -> begin
(no_reflect ())
end
| uu____1899 -> begin
(

let uu____1900 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1900) with
| (env_no_ex, topt) -> begin
(

let uu____1911 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_386 = (let _0_385 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _0_384 = (let _0_383 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_0_383)::[])
in (_0_385)::_0_384))
in ((repr), (_0_386)))))) None top.FStar_Syntax_Syntax.pos)
in (

let uu____1935 = (let _0_388 = (let _0_387 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _0_387 Prims.fst))
in (tc_tot_or_gtot_term _0_388 t))
in (match (uu____1935) with
| (t, uu____1952, g) -> begin
(

let uu____1954 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1954) with
| FStar_Syntax_Syntax.Tm_app (uu____1963, ((res, uu____1965))::((wp, uu____1967))::[]) -> begin
((t), (res), (wp), (g))
end
| uu____2001 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____1911) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____2025 = (

let uu____2028 = (tc_tot_or_gtot_term env_no_ex e)
in (match (uu____2028) with
| (e, c, g) -> begin
((

let uu____2038 = (let _0_389 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _0_389))
in (match (uu____2038) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____2043 -> begin
()
end));
(

let uu____2044 = (FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____2044) with
| None -> begin
((let _0_394 = (let _0_393 = (let _0_392 = (let _0_391 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _0_390 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _0_391 _0_390)))
in ((_0_392), (e.FStar_Syntax_Syntax.pos)))
in (_0_393)::[])
in (FStar_TypeChecker_Err.add_errors env _0_394));
(let _0_395 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_0_395)));
)
end
| Some (g') -> begin
(let _0_397 = (let _0_396 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _0_396))
in ((e), (_0_397)))
end));
)
end))
in (match (uu____2025) with
| (e, g) -> begin
(

let c = (let _0_402 = (FStar_Syntax_Syntax.mk_Comp (let _0_401 = (let _0_398 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (_0_398)::[])
in (let _0_400 = (let _0_399 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_399)::[])
in {FStar_Syntax_Syntax.comp_univs = _0_401; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _0_400; FStar_Syntax_Syntax.flags = []})))
in (FStar_All.pipe_right _0_402 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[]))))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____2080 = (comp_check_expected_typ env e c)
in (match (uu____2080) with
| (e, c, g') -> begin
(let _0_403 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_0_403)))
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

let env = (let _0_405 = (let _0_404 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _0_404 Prims.fst))
in (FStar_All.pipe_right _0_405 instantiate_both))
in ((

let uu____2113 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____2113) with
| true -> begin
(let _0_407 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _0_406 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _0_407 _0_406)))
end
| uu____2114 -> begin
()
end));
(

let uu____2115 = (tc_term (no_inst env) head)
in (match (uu____2115) with
| (head, chead, g_head) -> begin
(

let uu____2125 = (

let uu____2129 = ((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head))
in (match (uu____2129) with
| true -> begin
(let _0_408 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _0_408))
end
| uu____2133 -> begin
(let _0_409 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _0_409))
end))
in (match (uu____2125) with
| (e, c, g) -> begin
((

let uu____2141 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2141) with
| true -> begin
(let _0_410 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _0_410))
end
| uu____2142 -> begin
()
end));
(

let c = (

let uu____2144 = (((FStar_TypeChecker_Env.should_verify env) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____2144) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end
| uu____2145 -> begin
c
end))
in (

let uu____2146 = (comp_check_expected_typ env0 e c)
in (match (uu____2146) with
| (e, c, g') -> begin
(

let gimp = (

let uu____2157 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____2157) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____2159) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let uu___102_2191 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___102_2191.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___102_2191.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___102_2191.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____2216 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (let _0_411 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _0_411))
in ((

let uu____2219 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2219) with
| true -> begin
(let _0_413 = (FStar_Syntax_Print.term_to_string e)
in (let _0_412 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _0_413 _0_412)))
end
| uu____2220 -> begin
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

let uu____2249 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2249) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let uu____2261 = (tc_term env1 e1)
in (match (uu____2261) with
| (e1, c1, g1) -> begin
(

let uu____2271 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let uu____2277 = (FStar_Syntax_Util.type_u ())
in (match (uu____2277) with
| (k, uu____2283) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _0_414 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_0_414), (res_t))))
end))
end)
in (match (uu____2271) with
| (env_branches, res_t) -> begin
((

let uu____2291 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2291) with
| true -> begin
(let _0_415 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" _0_415))
end
| uu____2292 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____2342 = (

let uu____2345 = (FStar_List.fold_right (fun uu____2364 uu____2365 -> (match (((uu____2364), (uu____2365))) with
| ((uu____2397, f, c, g), (caccum, gaccum)) -> begin
(let _0_416 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_0_416)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____2345) with
| (cases, g) -> begin
(let _0_417 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_0_417), (g)))
end))
in (match (uu____2342) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let scrutinee = (FStar_TypeChecker_Util.maybe_lift env scrutinee c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____2499 -> (match (uu____2499) with
| ((pat, wopt, br), uu____2515, lc, uu____2517) -> begin
(let _0_418 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (_0_418)))
end))))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name)))))) None e.FStar_Syntax_Syntax.pos)))))
in (

let uu____2562 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____2562) with
| true -> begin
(mk_match e1)
end
| uu____2565 -> begin
(

let e_match = (mk_match (FStar_Syntax_Syntax.bv_to_name guard_x))
in (

let lb = (let _0_419 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _0_419; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_422 = (let _0_421 = (let _0_420 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_0_420)::[])
in (FStar_Syntax_Subst.close _0_421 e_match))
in ((((false), ((lb)::[]))), (_0_422)))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____2586 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2586) with
| true -> begin
(let _0_425 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _0_424 = (let _0_423 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _0_423))
in (FStar_Util.print2 "(%s) comp type = %s\n" _0_425 _0_424)))
end
| uu____2587 -> begin
()
end));
(let _0_426 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_0_426)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2590); FStar_Syntax_Syntax.lbunivs = uu____2591; FStar_Syntax_Syntax.lbtyp = uu____2592; FStar_Syntax_Syntax.lbeff = uu____2593; FStar_Syntax_Syntax.lbdef = uu____2594})::[]), uu____2595) -> begin
((

let uu____2610 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2610) with
| true -> begin
(let _0_427 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _0_427))
end
| uu____2611 -> begin
()
end));
(check_top_level_let env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____2612), uu____2613) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2623); FStar_Syntax_Syntax.lbunivs = uu____2624; FStar_Syntax_Syntax.lbtyp = uu____2625; FStar_Syntax_Syntax.lbeff = uu____2626; FStar_Syntax_Syntax.lbdef = uu____2627})::uu____2628), uu____2629) -> begin
((

let uu____2645 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2645) with
| true -> begin
(let _0_428 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _0_428))
end
| uu____2646 -> begin
()
end));
(check_top_level_let_rec env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____2647), uu____2648) -> begin
(check_inner_let_rec env top)
end));
)))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let uu____2692 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____2692) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____2705 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2705) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____2708 -> begin
FStar_Util.Inr ((let _0_429 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_429)))
end))
in (

let is_data_ctor = (fun uu___91_2715 -> (match (uu___91_2715) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| uu____2718 -> begin
false
end))
in (

let uu____2720 = ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v))))
in (match (uu____2720) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_431 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _0_430 = (FStar_TypeChecker_Env.get_range env)
in ((_0_431), (_0_430)))))))
end
| uu____2731 -> begin
(value_check_expected_typ env e tc implicits)
end))))
end)))
in (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(failwith (let _0_432 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _0_432)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____2756 = (FStar_Syntax_Subst.compress t1).FStar_Syntax_Syntax.n
in (match (uu____2756) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2757) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____2765 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___103_2785 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___103_2785.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___103_2785.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___103_2785.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____2813 = (

let uu____2820 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____2820) with
| None -> begin
(

let uu____2828 = (FStar_Syntax_Util.type_u ())
in (match (uu____2828) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____2813) with
| (t, uu____2849, g0) -> begin
(

let uu____2857 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (uu____2857) with
| (e, uu____2868, g1) -> begin
(let _0_435 = (let _0_433 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _0_433 FStar_Syntax_Util.lcomp_of_comp))
in (let _0_434 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_0_435), (_0_434))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (match (env.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____2882 -> begin
(FStar_TypeChecker_Env.lookup_bv env x)
end)
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let uu___104_2884 = x
in {FStar_Syntax_Syntax.ppname = uu___104_2884.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_2884.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let uu____2885 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____2885) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____2898 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2898) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____2901 -> begin
FStar_Util.Inr ((let _0_436 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_436)))
end))
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____2905; FStar_Syntax_Syntax.pos = uu____2906; FStar_Syntax_Syntax.vars = uu____2907}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let uu____2915 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2915) with
| (us', t) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_437 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_0_437))))))
end
| uu____2932 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____2939 -> begin
(failwith "Impossible")
end)) us' us)
end);
(

let fv' = (

let uu___105_2941 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___106_2942 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___106_2942.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___106_2942.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___105_2941.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___105_2941.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _0_438 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_438 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2975 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2975) with
| (us, t) -> begin
((

let uu____2988 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Range")))
in (match (uu____2988) with
| true -> begin
(let _0_443 = (FStar_Syntax_Print.lid_to_string (FStar_Syntax_Syntax.lid_of_fv fv))
in (let _0_442 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _0_441 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid (FStar_Syntax_Syntax.lid_of_fv fv)))
in (let _0_440 = (FStar_Range.string_of_use_range (FStar_Ident.range_of_lid (FStar_Syntax_Syntax.lid_of_fv fv)))
in (let _0_439 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s" _0_443 _0_442 _0_441 _0_440 _0_439))))))
end
| uu____2989 -> begin
()
end));
(

let fv' = (

let uu___107_2991 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___108_2992 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___108_2992.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___108_2992.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___107_2991.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___107_2991.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _0_444 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_444 us))
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

let uu____3049 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3049) with
| (bs, c) -> begin
(

let env0 = env
in (

let uu____3058 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3058) with
| (env, uu____3066) -> begin
(

let uu____3069 = (tc_binders env bs)
in (match (uu____3069) with
| (bs, env, g, us) -> begin
(

let uu____3081 = (tc_comp env c)
in (match (uu____3081) with
| (c, uc, f) -> begin
(

let e = (

let uu___109_3094 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = uu___109_3094.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___109_3094.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___109_3094.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env e bs c);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _0_445 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _0_445))
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

let uu____3149 = (let _0_447 = (let _0_446 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_446)::[])
in (FStar_Syntax_Subst.open_term _0_447 phi))
in (match (uu____3149) with
| (x, phi) -> begin
(

let env0 = env
in (

let uu____3158 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3158) with
| (env, uu____3166) -> begin
(

let uu____3169 = (let _0_448 = (FStar_List.hd x)
in (tc_binder env _0_448))
in (match (uu____3169) with
| (x, env, f1, u) -> begin
((

let uu____3190 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____3190) with
| true -> begin
(let _0_451 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _0_450 = (FStar_Syntax_Print.term_to_string phi)
in (let _0_449 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _0_451 _0_450 _0_449))))
end
| uu____3191 -> begin
()
end));
(

let uu____3192 = (FStar_Syntax_Util.type_u ())
in (match (uu____3192) with
| (t_phi, uu____3199) -> begin
(

let uu____3200 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (uu____3200) with
| (phi, uu____3208, f2) -> begin
(

let e = (

let uu___110_3213 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = uu___110_3213.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___110_3213.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___110_3213.FStar_Syntax_Syntax.vars})
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _0_452 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _0_452))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____3240) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in ((

let uu____3265 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3265) with
| true -> begin
(let _0_453 = (FStar_Syntax_Print.term_to_string (

let uu___111_3266 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = uu___111_3266.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___111_3266.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___111_3266.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _0_453))
end
| uu____3284 -> begin
()
end));
(

let uu____3285 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3285) with
| (bs, body) -> begin
(tc_abs env top bs body)
end));
))
end
| uu____3293 -> begin
(failwith (let _0_455 = (FStar_Syntax_Print.term_to_string top)
in (let _0_454 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _0_455 _0_454))))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (uu____3299) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (uu____3300, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (uu____3306, Some (uu____3307)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____3315) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (uu____3319) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (uu____3320) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____3321) -> begin
FStar_TypeChecker_Common.t_range
end
| uu____3322 -> begin
(Prims.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____3333) -> begin
(

let uu____3340 = (FStar_Syntax_Util.type_u ())
in (match (uu____3340) with
| (k, u) -> begin
(

let uu____3348 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3348) with
| (t, uu____3356, g) -> begin
(let _0_456 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((_0_456), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____3359) -> begin
(

let uu____3366 = (FStar_Syntax_Util.type_u ())
in (match (uu____3366) with
| (k, u) -> begin
(

let uu____3374 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3374) with
| (t, uu____3382, g) -> begin
(let _0_457 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((_0_457), (u), (g)))
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

let tc = ((let _0_459 = (let _0_458 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_0_458)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _0_459)) None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos)
in (

let uu____3403 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____3403) with
| (tc, uu____3411, f) -> begin
(

let uu____3413 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3413) with
| (head, args) -> begin
(

let comp_univs = (

let uu____3443 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____3443) with
| FStar_Syntax_Syntax.Tm_uinst (uu____3444, us) -> begin
us
end
| uu____3450 -> begin
[]
end))
in (

let uu____3451 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3451) with
| (uu____3464, args) -> begin
(

let uu____3480 = (let _0_461 = (FStar_List.hd args)
in (let _0_460 = (FStar_List.tl args)
in ((_0_461), (_0_460))))
in (match (uu____3480) with
| (res, args) -> begin
(

let uu____3532 = (let _0_462 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___92_3550 -> (match (uu___92_3550) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____3556 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3556) with
| (env, uu____3563) -> begin
(

let uu____3566 = (tc_tot_or_gtot_term env e)
in (match (uu____3566) with
| (e, uu____3573, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _0_462 FStar_List.unzip))
in (match (uu____3532) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let uu___112_3589 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___112_3589.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = uu___112_3589.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____3593 = (FStar_TypeChecker_Util.effect_repr env c u)
in (match (uu____3593) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (let _0_463 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_0_463))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____3603) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
FStar_Syntax_Syntax.U_succ ((aux u))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
FStar_Syntax_Syntax.U_max ((FStar_List.map aux us))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____3609 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _0_464 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_464 Prims.snd))
end
| uu____3612 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (Prims.raise (FStar_Errors.Error ((let _0_465 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_0_465), (top.FStar_Syntax_Syntax.pos)))))))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun uu____3690 bs bs_expected -> (match (uu____3690) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
((match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_468 = (let _0_466 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _0_466))
in (let _0_467 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_0_468), (_0_467)))))))
end
| uu____3787 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____3791 = (

let uu____3794 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
in (match (uu____3794) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____3797 -> begin
((

let uu____3799 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____3799) with
| true -> begin
(let _0_469 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _0_469))
end
| uu____3800 -> begin
()
end));
(

let uu____3801 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (uu____3801) with
| (t, uu____3808, g1) -> begin
(

let g2 = (let _0_471 = (FStar_TypeChecker_Env.get_range env)
in (let _0_470 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _0_471 "Type annotation on parameter incompatible with the expected type" _0_470)))
in (

let g = (let _0_472 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _0_472))
in ((t), (g))))
end));
)
end))
in (match (uu____3791) with
| (t, g) -> begin
(

let hd = (

let uu___113_3827 = hd
in {FStar_Syntax_Syntax.ppname = uu___113_3827.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___113_3827.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _0_473 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _0_473))
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
| uu____3929 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____3933 = (tc_binders env bs)
in (match (uu____3933) with
| (bs, envbody, g, uu____3952) -> begin
(

let uu____3953 = (

let uu____3958 = (FStar_Syntax_Subst.compress body).FStar_Syntax_Syntax.n
in (match (uu____3958) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), uu____3965) -> begin
(

let uu____3984 = (tc_comp envbody c)
in (match (uu____3984) with
| (c, uu____3993, g') -> begin
(let _0_474 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_0_474)))
end))
end
| uu____3996 -> begin
((None), (body), (g))
end))
in (match (uu____3953) with
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

let uu____4046 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____4046) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
((match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4075 -> begin
(failwith "Impossible")
end);
(

let uu____4079 = (tc_binders env bs)
in (match (uu____4079) with
| (bs, envbody, g, uu____4099) -> begin
(

let uu____4100 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____4100) with
| (envbody, uu____4117) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____4128) -> begin
(

let uu____4133 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (uu____4133) with
| (uu____4158, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____4194 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____4194) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun uu____4255 c_expected -> (match (uu____4255) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _0_475 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_0_475)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.arrow more_bs_expected c_expected))
in (let _0_476 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_0_476))))
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

let uu____4372 = (check_binders env more_bs bs_expected)
in (match (uu____4372) with
| (env, bs', more, guard', subst) -> begin
(let _0_478 = (let _0_477 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_0_477), (subst)))
in (handle_more _0_478 c_expected))
end))
end
| uu____4420 -> begin
(let _0_480 = (let _0_479 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _0_479))
in (fail _0_480 t))
end))
end
| uu____4428 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end))
end)
end))
in (let _0_481 = (check_binders env bs bs_expected)
in (handle_more _0_481 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let uu___114_4458 = envbody
in {FStar_TypeChecker_Env.solver = uu___114_4458.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_4458.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_4458.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_4458.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_4458.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_4458.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_4458.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_4458.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_4458.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_4458.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_4458.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_4458.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___114_4458.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_4458.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_4458.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___114_4458.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_4458.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___114_4458.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_4458.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___114_4458.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_4458.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_4458.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_4458.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____4472 uu____4473 -> (match (((uu____4472), (uu____4473))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let uu____4498 = (let _0_483 = (let _0_482 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _0_482 Prims.fst))
in (tc_term _0_483 t))
in (match (uu____4498) with
| (t, uu____4510, uu____4511) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _0_484 = (FStar_Syntax_Syntax.mk_binder (

let uu___115_4518 = x
in {FStar_Syntax_Syntax.ppname = uu___115_4518.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_4518.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_0_484)::letrec_binders)
end
| uu____4519 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let uu____4522 = (check_actuals_against_formals env bs bs_expected)
in (match (uu____4522) with
| (envbody, bs, g, c) -> begin
(

let uu____4552 = (

let uu____4556 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____4556) with
| true -> begin
(mk_letrec_env envbody bs c)
end
| uu____4560 -> begin
((envbody), ([]))
end))
in (match (uu____4552) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| uu____4589 -> begin
(match ((not (norm))) with
| true -> begin
(let _0_485 = (unfold_whnf env t)
in (as_function_typ true _0_485))
end
| uu____4602 -> begin
(

let uu____4603 = (expected_function_typ env None body)
in (match (uu____4603) with
| (uu____4627, bs, uu____4629, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end)
end)))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____4650 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____4650) with
| (env, topt) -> begin
((

let uu____4662 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____4662) with
| true -> begin
(let _0_486 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _0_486 (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____4664 -> begin
"false"
end)))
end
| uu____4665 -> begin
()
end));
(

let uu____4666 = (expected_function_typ env topt body)
in (match (uu____4666) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let uu____4696 = (tc_term (

let uu___116_4700 = envbody
in {FStar_TypeChecker_Env.solver = uu___116_4700.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___116_4700.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___116_4700.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___116_4700.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___116_4700.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___116_4700.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___116_4700.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___116_4700.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___116_4700.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___116_4700.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___116_4700.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___116_4700.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___116_4700.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___116_4700.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___116_4700.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___116_4700.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___116_4700.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___116_4700.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___116_4700.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___116_4700.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___116_4700.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___116_4700.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (uu____4696) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in ((

let uu____4709 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))
in (match (uu____4709) with
| true -> begin
(let _0_489 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _0_488 = (let _0_487 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _0_487))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _0_489 _0_488)))
end
| uu____4718 -> begin
()
end));
(

let uu____4719 = (let _0_491 = (let _0_490 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_0_490)))
in (check_expected_effect (

let uu___117_4723 = envbody
in {FStar_TypeChecker_Env.solver = uu___117_4723.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_4723.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_4723.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_4723.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_4723.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_4723.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_4723.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_4723.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_4723.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_4723.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_4723.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_4723.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_4723.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___117_4723.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___117_4723.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___117_4723.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_4723.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___117_4723.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___117_4723.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___117_4723.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_4723.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___117_4723.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___117_4723.FStar_TypeChecker_Env.qname_and_index}) c_opt _0_491))
in (match (uu____4719) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = (

let uu____4734 = (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env))))
in (match (uu____4734) with
| true -> begin
(let _0_492 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _0_492))
end
| uu____4735 -> begin
(

let guard = (let _0_493 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _0_493))
in guard)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _0_496 = Some ((let _0_495 = (FStar_All.pipe_right (FStar_Util.dflt cbody c_opt) FStar_Syntax_Util.lcomp_of_comp)
in (FStar_All.pipe_right _0_495 (fun _0_494 -> FStar_Util.Inl (_0_494)))))
in (FStar_Syntax_Util.abs bs body _0_496))
in (

let uu____4756 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4771) -> begin
((e), (t), (guard))
end
| uu____4779 -> begin
(

let uu____4780 = (match (use_teq) with
| true -> begin
(let _0_497 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_0_497)))
end
| uu____4785 -> begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end)
in (match (uu____4780) with
| (e, guard') -> begin
(let _0_498 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_0_498)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (uu____4756) with
| (e, tfun, guard) -> begin
(

let c = (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____4802 -> begin
(FStar_TypeChecker_Util.return_value env tfun e)
end)
in (

let uu____4803 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (uu____4803) with
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

let uu____4839 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____4839) with
| true -> begin
(let _0_500 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _0_499 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _0_500 _0_499)))
end
| uu____4840 -> begin
()
end));
(

let monadic_application = (fun uu____4881 subst arg_comps_rev arg_rets guard fvs bs -> (match (uu____4881) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___118_4922 = cres
in {FStar_Syntax_Syntax.eff_name = uu___118_4922.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___118_4922.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___118_4922.FStar_Syntax_Syntax.comp})
in (

let uu____4923 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun uu___93_4950 -> (match (uu___93_4950) with
| (uu____4959, uu____4960, FStar_Util.Inl (uu____4961)) -> begin
false
end
| (uu____4972, uu____4973, FStar_Util.Inr (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = (match (refine_with_equality) with
| true -> begin
(let _0_501 = ((FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets)) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _0_501 cres))
end
| uu____4994 -> begin
((

let uu____4996 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____4996) with
| true -> begin
(let _0_504 = (FStar_Syntax_Print.term_to_string head)
in (let _0_503 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _0_502 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _0_504 _0_503 _0_502))))
end
| uu____4997 -> begin
()
end));
cres;
)
end)
in ((cres), (g))))))
end
| uu____4998 -> begin
(

let g = (let _0_505 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _0_505 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _0_509 = (let _0_508 = (FStar_Syntax_Syntax.mk_Total (let _0_507 = (let _0_506 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _0_506))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _0_507)))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_508))
in ((_0_509), (g))))
end)
in (match (uu____4923) with
| (cres, guard) -> begin
((

let uu____5011 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5011) with
| true -> begin
(let _0_510 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _0_510))
end
| uu____5012 -> begin
()
end));
(

let uu____5013 = (FStar_List.fold_left (fun uu____5036 uu____5037 -> (match (((uu____5036), (uu____5037))) with
| ((args, out_c, monadic), ((e, q), x, c)) -> begin
(match (c) with
| FStar_Util.Inl (eff_name, arg_typ) -> begin
(let _0_513 = (let _0_512 = (let _0_511 = (FStar_TypeChecker_Util.maybe_lift env e eff_name out_c.FStar_Syntax_Syntax.eff_name arg_typ)
in ((_0_511), (q)))
in (_0_512)::args)
in ((_0_513), (out_c), (monadic)))
end
| FStar_Util.Inr (c) -> begin
(

let monadic = (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c))))
in (

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c ((x), (out_c)))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (((((e), (q)))::args), (out_c), (monadic))))))
end)
end)) (([]), (cres), (false)) arg_comps_rev)
in (match (uu____5013) with
| (args, comp, monadic) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead ((None), (comp)))
in (

let app = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (

let uu____5172 = (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp comp))))
in (match (uu____5172) with
| true -> begin
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
end
| uu____5173 -> begin
app
end))
in (

let uu____5174 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (uu____5174) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____5232 bs args -> (match (uu____5232) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (uu____5327))))::rest, ((uu____5329, None))::uu____5330) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let uu____5367 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (uu____5367) with
| (varg, uu____5378, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _0_514 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_0_514)))
in (let _0_516 = (let _0_515 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (FStar_Util.Inl (((FStar_Syntax_Const.effect_Tot_lid), (t))))))::outargs), ((arg)::arg_rets), (_0_515), (fvs)))
in (tc_args head_info _0_516 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| uu____5481 -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___119_5488 = x
in {FStar_Syntax_Syntax.ppname = uu___119_5488.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_5488.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____5490 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____5490) with
| true -> begin
(let _0_517 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _0_517))
end
| uu____5491 -> begin
()
end));
(

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let uu___120_5495 = env
in {FStar_TypeChecker_Env.solver = uu___120_5495.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___120_5495.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___120_5495.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___120_5495.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___120_5495.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___120_5495.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___120_5495.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___120_5495.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___120_5495.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___120_5495.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___120_5495.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___120_5495.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___120_5495.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___120_5495.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___120_5495.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___120_5495.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___120_5495.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___120_5495.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___120_5495.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___120_5495.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___120_5495.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___120_5495.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___120_5495.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____5497 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5497) with
| true -> begin
(let _0_520 = (FStar_Syntax_Print.tag_of_term e)
in (let _0_519 = (FStar_Syntax_Print.term_to_string e)
in (let _0_518 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _0_520 _0_519 _0_518))))
end
| uu____5498 -> begin
()
end));
(

let uu____5499 = (tc_term env e)
in (match (uu____5499) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in (

let uu____5515 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____5515) with
| true -> begin
(

let subst = (let _0_521 = (FStar_List.hd bs)
in (maybe_extend_subst subst _0_521 e))
in (tc_args head_info ((subst), ((((arg), (None), (FStar_Util.Inl (((c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ))))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____5574 -> begin
(

let uu____5575 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name)
in (match (uu____5575) with
| true -> begin
(

let subst = (let _0_522 = (FStar_List.hd bs)
in (maybe_extend_subst subst _0_522 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____5624 -> begin
(

let uu____5625 = (FStar_Syntax_Syntax.is_null_binder (FStar_List.hd bs))
in (match (uu____5625) with
| true -> begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _0_523 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_523))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end
| uu____5670 -> begin
(let _0_526 = (let _0_525 = (let _0_524 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name x))
in (_0_524)::arg_rets)
in ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), (_0_525), (g), ((x)::fvs)))
in (tc_args head_info _0_526 rest rest'))
end))
end))
end))))
end));
))));
)));
)
end
| (uu____5707, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____5728) -> begin
(

let uu____5758 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (uu____5758) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _0_527 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _0_527 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let uu____5796 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (uu____5796) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in ((

let uu____5810 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5810) with
| true -> begin
(let _0_528 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _0_528))
end
| uu____5811 -> begin
()
end));
(tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args);
))
end))
end
| uu____5840 when (not (norm)) -> begin
(let _0_529 = (unfold_whnf env tres)
in (aux true _0_529))
end
| uu____5841 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_533 = (let _0_531 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _0_530 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _0_531 _0_530)))
in (let _0_532 = (FStar_Syntax_Syntax.argpos arg)
in ((_0_533), (_0_532)))))))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (

let uu____5860 = (FStar_Syntax_Util.unrefine tf).FStar_Syntax_Syntax.n
in (match (uu____5860) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let uu____5934 = (tc_term env e)
in (match (uu____5934) with
| (e, c, g_e) -> begin
(

let uu____5947 = (tc_args env tl)
in (match (uu____5947) with
| (args, comps, g_rest) -> begin
(let _0_534 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_0_534)))
end))
end))
end))
in (

let uu____5979 = (tc_args env args)
in (match (uu____5979) with
| (args, comps, g_args) -> begin
(

let bs = (FStar_Syntax_Util.null_binders_of_tks (FStar_All.pipe_right comps (FStar_List.map (fun uu____6020 -> (match (uu____6020) with
| (uu____6028, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end)))))
in (

let ml_or_tot = (

let uu____6038 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)
in (match (uu____6038) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| uu____6046 -> begin
FStar_Syntax_Util.ml_comp
end))
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(

let uu____6058 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____6058) with
| FStar_Syntax_Syntax.Tm_type (uu____6063) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| uu____6066 -> begin
ml_or_tot
end))
end)
in (

let cres = (let _0_537 = (let _0_536 = (let _0_535 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_535 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _0_536))
in (ml_or_tot _0_537 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____6074 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6074) with
| true -> begin
(let _0_540 = (FStar_Syntax_Print.term_to_string head)
in (let _0_539 = (FStar_Syntax_Print.term_to_string tf)
in (let _0_538 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _0_540 _0_539 _0_538))))
end
| uu____6075 -> begin
()
end));
(let _0_541 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _0_541));
(

let comp = (let _0_542 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____6080 out -> (match (uu____6080) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _0_542))
in (let _0_544 = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _0_543 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_0_544), (comp), (_0_543)))));
))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6111 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6111) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| uu____6154 -> begin
(match ((not (norm))) with
| true -> begin
(let _0_545 = (unfold_whnf env tf)
in (check_function_app true _0_545))
end
| uu____6160 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_546 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((_0_546), (head.FStar_Syntax_Syntax.pos))))))
end)
end)))
in (let _0_548 = (let _0_547 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _0_547))
in (check_function_app false _0_548)))));
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

let uu____6211 = (FStar_List.fold_left2 (fun uu____6224 uu____6225 uu____6226 -> (match (((uu____6224), (uu____6225), (uu____6226))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((aq <> aq')) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____6269 -> begin
()
end);
(

let uu____6270 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____6270) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _0_549 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _0_549 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _0_553 = (let _0_551 = (let _0_550 = (FStar_Syntax_Syntax.as_arg e)
in (_0_550)::[])
in (FStar_List.append seen _0_551))
in (let _0_552 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_0_553), (_0_552), (ghost)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____6211) with
| (args, guard, ghost) -> begin
(

let e = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = (match (ghost) with
| true -> begin
(let _0_554 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _0_554 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____6315 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____6316 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (uu____6316) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| uu____6328 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let uu____6350 = (FStar_Syntax_Subst.open_branch branch)
in (match (uu____6350) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____6376 = branch
in (match (uu____6376) with
| (cpat, uu____6396, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let uu____6438 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (uu____6438) with
| (pat_bvs, exps, p) -> begin
((

let uu____6460 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6460) with
| true -> begin
(let _0_556 = (FStar_Syntax_Print.pat_to_string p0)
in (let _0_555 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _0_556 _0_555)))
end
| uu____6461 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let uu____6463 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____6463) with
| (env1, uu____6476) -> begin
(

let env1 = (

let uu___121_6480 = env1
in {FStar_TypeChecker_Env.solver = uu___121_6480.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___121_6480.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___121_6480.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___121_6480.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___121_6480.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___121_6480.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___121_6480.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___121_6480.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___121_6480.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___121_6480.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___121_6480.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___121_6480.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___121_6480.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___121_6480.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___121_6480.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___121_6480.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___121_6480.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___121_6480.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___121_6480.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___121_6480.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___121_6480.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___121_6480.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___121_6480.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let uu____6482 = (let _0_572 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> ((

let uu____6502 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6502) with
| true -> begin
(let _0_558 = (FStar_Syntax_Print.term_to_string e)
in (let _0_557 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _0_558 _0_557)))
end
| uu____6503 -> begin
()
end));
(

let uu____6504 = (tc_term env1 e)
in (match (uu____6504) with
| (e, lc, g) -> begin
((

let uu____6514 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6514) with
| true -> begin
(let _0_560 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _0_559 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _0_560 _0_559)))
end
| uu____6515 -> begin
()
end));
(

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let uu____6518 = (let _0_561 = (FStar_TypeChecker_Rel.discharge_guard env (

let uu___122_6519 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___122_6519.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___122_6519.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___122_6519.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _0_561 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _0_563 = (let _0_562 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _0_562 (FStar_List.map (fun uu____6553 -> (match (uu____6553) with
| (u, uu____6558) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _0_563 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____6570 = (let _0_564 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _0_564))
in (match (uu____6570) with
| true -> begin
(

let unresolved = (let _0_565 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _0_565 FStar_Util.set_elements))
in (Prims.raise (FStar_Errors.Error ((let _0_570 = (let _0_569 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _0_568 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _0_567 = (let _0_566 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____6598 -> (match (uu____6598) with
| (u, uu____6606) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _0_566 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _0_569 _0_568 _0_567))))
in ((_0_570), (p.FStar_Syntax_Syntax.p)))))))
end
| uu____6618 -> begin
()
end));
(

let uu____6620 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6620) with
| true -> begin
(let _0_571 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _0_571))
end
| uu____6621 -> begin
()
end));
((e), (e'));
))))))));
)
end));
))))
in (FStar_All.pipe_right _0_572 FStar_List.unzip))
in (match (uu____6482) with
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

let uu____6644 = (let _0_573 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _0_573 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____6644) with
| (scrutinee_env, uu____6660) -> begin
(

let uu____6663 = (tc_pat true pat_t pattern)
in (match (uu____6663) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let uu____6691 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
(

let uu____6706 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____6706) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____6713 -> begin
(

let uu____6714 = (let _0_574 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _0_574 e))
in (match (uu____6714) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end))
end)
in (match (uu____6691) with
| (when_clause, g_when) -> begin
(

let uu____6737 = (tc_term pat_env branch_exp)
in (match (uu____6737) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _0_576 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _0_575 -> Some (_0_575)) _0_576))
end)
in (

let uu____6769 = (

let eqs = (

let uu____6777 = (not ((FStar_TypeChecker_Env.should_verify env)))
in (match (uu____6777) with
| true -> begin
None
end
| uu____6783 -> begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| uu____6803 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _0_578 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _0_577 -> Some (_0_577)) _0_578))
end))
end))) None))
end))
in (

let uu____6832 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (uu____6832) with
| (c, g_branch) -> begin
(

let uu____6842 = (match (((eqs), (when_condition))) with
| uu____6853 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _0_580 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _0_579 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_0_580), (_0_579))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = FStar_TypeChecker_Common.NonTrivial ((FStar_Syntax_Util.mk_conj f w))
in (let _0_583 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _0_582 = (let _0_581 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _0_581 g_when))
in ((_0_583), (_0_582))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _0_584 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_0_584), (g_when)))))
end)
in (match (uu____6842) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _0_586 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _0_585 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_0_586), (_0_585), (g_branch)))))
end))
end)))
in (match (uu____6769) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let uu____6939 = (not ((FStar_TypeChecker_Env.should_verify env)))
in (match (uu____6939) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____6940 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> (

let uu____6972 = (let _0_588 = (FStar_List.length (let _0_587 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _0_587)))
in (_0_588 > (Prims.parse_int "1")))
in (match (uu____6972) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____6984 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____6984) with
| None -> begin
[]
end
| uu____6995 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational None)
in (

let disc = ((let _0_590 = (let _0_589 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_0_589)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _0_590)) None scrutinee_tm.FStar_Syntax_Syntax.pos)
in (let _0_591 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_0_591)::[])))
end)))
end
| uu____7011 -> begin
[]
end)))
in (

let fail = (fun uu____7020 -> (failwith (let _0_594 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _0_593 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _0_592 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _0_594 _0_593 _0_592))))))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____7041) -> begin
(head_constructor t)
end
| uu____7047 -> begin
(fail ())
end))
in (

let pat_exp = (let _0_595 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _0_595 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____7065) -> begin
(let _0_600 = ((let _0_599 = (let _0_598 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _0_597 = (let _0_596 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_0_596)::[])
in (_0_598)::_0_597))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _0_599)) None scrutinee_tm.FStar_Syntax_Syntax.pos)
in (_0_600)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in (

let uu____7083 = (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)))
in (match (uu____7083) with
| true -> begin
[]
end
| uu____7089 -> begin
(let _0_601 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _0_601))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in (

let uu____7113 = (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)))
in (match (uu____7113) with
| true -> begin
[]
end
| uu____7119 -> begin
(

let sub_term_guards = (let _0_605 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____7138 -> (match (uu____7138) with
| (ei, uu____7145) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____7155 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____7155) with
| None -> begin
[]
end
| uu____7162 -> begin
(

let sub_term = ((let _0_604 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (let _0_603 = (let _0_602 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_0_602)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_604 _0_603))) None f.FStar_Syntax_Syntax.p)
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right _0_605 FStar_List.flatten))
in (let _0_606 = (discriminate scrutinee_tm f)
in (FStar_List.append _0_606 sub_term_guards)))
end)))
end
| uu____7185 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> (

let uu____7197 = (not ((FStar_TypeChecker_Env.should_verify env)))
in (match (uu____7197) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end
| uu____7198 -> begin
(

let t = (let _0_607 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _0_607))
in (

let uu____7201 = (FStar_Syntax_Util.type_u ())
in (match (uu____7201) with
| (k, uu____7205) -> begin
(

let uu____7206 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____7206) with
| (t, uu____7211, uu____7212) -> begin
t
end))
end)))
end)))
in (

let branch_guard = (let _0_608 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _0_608 FStar_Syntax_Util.mk_disj_l))
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

let uu____7229 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7229) with
| true -> begin
(let _0_609 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _0_609))
end
| uu____7230 -> begin
()
end));
(let _0_610 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_0_610), (branch_guard), (c), (guard)));
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

let uu____7248 = (check_let_bound_def true env lb)
in (match (uu____7248) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let uu____7262 = (match ((annotated && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
((g1), (e1), (univ_vars), (c1))
end
| uu____7271 -> begin
(

let g1 = (let _0_611 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _0_611 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____7274 = (FStar_List.hd (let _0_614 = (let _0_613 = (let _0_612 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_0_612)))
in (_0_613)::[])
in (FStar_TypeChecker_Util.generalize env _0_614)))
in (match (uu____7274) with
| (uu____7305, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end)
in (match (uu____7262) with
| (g1, e1, univ_vars, c1) -> begin
(

let uu____7316 = (

let uu____7321 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____7321) with
| true -> begin
(

let uu____7326 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (uu____7326) with
| (ok, c1) -> begin
(match (ok) with
| true -> begin
((e2), (c1))
end
| uu____7341 -> begin
((

let uu____7343 = (FStar_Options.warn_top_level_effects ())
in (match (uu____7343) with
| true -> begin
(let _0_615 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.warn _0_615 FStar_TypeChecker_Err.top_level_effect))
end
| uu____7344 -> begin
()
end));
(let _0_616 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))))) None e2.FStar_Syntax_Syntax.pos)
in ((_0_616), (c1)));
)
end)
end))
end
| uu____7361 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let c = (let _0_617 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right _0_617 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c)));
)
end))
in (match (uu____7316) with
| (e2, c1) -> begin
(

let cres = (let _0_618 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_618))
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _0_619 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_0_619), (cres), (FStar_TypeChecker_Rel.trivial_guard))));
))
end))
end))
end))
end
| uu____7406 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let uu___123_7427 = env
in {FStar_TypeChecker_Env.solver = uu___123_7427.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___123_7427.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___123_7427.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___123_7427.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___123_7427.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___123_7427.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___123_7427.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___123_7427.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___123_7427.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___123_7427.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___123_7427.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___123_7427.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___123_7427.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___123_7427.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___123_7427.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___123_7427.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___123_7427.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___123_7427.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___123_7427.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___123_7427.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___123_7427.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___123_7427.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___123_7427.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____7428 = (let _0_621 = (let _0_620 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _0_620 Prims.fst))
in (check_let_bound_def false _0_621 lb))
in (match (uu____7428) with
| (e1, uu____7442, c1, g1, annotated) -> begin
(

let x = (

let uu___124_7447 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___124_7447.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_7447.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____7448 = (let _0_623 = (let _0_622 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_622)::[])
in (FStar_Syntax_Subst.open_term _0_623 e2))
in (match (uu____7448) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let uu____7462 = (let _0_624 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _0_624 e2))
in (match (uu____7462) with
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

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_625 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_0_625)))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _0_628 = (let _0_627 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _0_627 e1))
in (FStar_All.pipe_left (fun _0_626 -> FStar_TypeChecker_Common.NonTrivial (_0_626)) _0_628))
in (

let g2 = (let _0_630 = (let _0_629 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _0_629 g2))
in (FStar_TypeChecker_Rel.close_guard xb _0_630))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (

let uu____7500 = (FStar_Option.isSome (FStar_TypeChecker_Env.expected_typ env))
in (match (uu____7500) with
| true -> begin
(

let tt = (let _0_631 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right _0_631 FStar_Option.get))
in ((

let uu____7507 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____7507) with
| true -> begin
(let _0_633 = (FStar_Syntax_Print.term_to_string tt)
in (let _0_632 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" _0_633 _0_632)))
end
| uu____7508 -> begin
()
end));
((e), (cres), (guard));
))
end
| uu____7509 -> begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____7512 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____7512) with
| true -> begin
(let _0_635 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (let _0_634 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" _0_635 _0_634)))
end
| uu____7513 -> begin
()
end));
((e), ((

let uu___125_7514 = cres
in {FStar_Syntax_Syntax.eff_name = uu___125_7514.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___125_7514.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___125_7514.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____7515 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____7536 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____7536) with
| (lbs, e2) -> begin
(

let uu____7547 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____7547) with
| (env0, topt) -> begin
(

let uu____7558 = (build_let_rec_env true env0 lbs)
in (match (uu____7558) with
| (lbs, rec_env) -> begin
(

let uu____7569 = (check_let_recs rec_env lbs)
in (match (uu____7569) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _0_636 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _0_636 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _0_638 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _0_638 (fun _0_637 -> Some (_0_637))))
in (

let lbs = (match ((not (env.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (match ((lb.FStar_Syntax_Syntax.lbunivs = [])) with
| true -> begin
lb
end
| uu____7598 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end))))
end
| uu____7599 -> begin
(

let ecs = (let _0_640 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _0_639 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_0_639))))))
in (FStar_TypeChecker_Util.generalize env _0_640))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____7642 -> (match (uu____7642) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (let _0_641 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_641))
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let uu____7673 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____7673) with
| (lbs, e2) -> begin
(let _0_643 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _0_642 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_0_643), (cres), (_0_642))))
end));
)))))
end))
end))
end))
end))
end
| uu____7702 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____7723 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____7723) with
| (lbs, e2) -> begin
(

let uu____7734 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____7734) with
| (env0, topt) -> begin
(

let uu____7745 = (build_let_rec_env false env0 lbs)
in (match (uu____7745) with
| (lbs, rec_env) -> begin
(

let uu____7756 = (check_let_recs rec_env lbs)
in (match (uu____7756) with
| (lbs, g_lbs) -> begin
(

let uu____7767 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let uu___126_7778 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___126_7778.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___126_7778.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let uu___127_7780 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___127_7780.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___127_7780.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___127_7780.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___127_7780.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (uu____7767) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____7797 = (tc_term env e2)
in (match (uu____7797) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___128_7811 = cres
in {FStar_Syntax_Syntax.eff_name = uu___128_7811.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___128_7811.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___128_7811.FStar_Syntax_Syntax.comp})
in (

let uu____7812 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____7812) with
| (lbs, e2) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (uu____7841) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let uu___129_7846 = cres
in {FStar_Syntax_Syntax.eff_name = uu___129_7846.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___129_7846.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___129_7846.FStar_Syntax_Syntax.comp})
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
| uu____7849 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let uu____7865 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____7865) with
| (uu____7871, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let uu____7882 = (FStar_List.fold_left (fun uu____7889 lb -> (match (uu____7889) with
| (lbs, env) -> begin
(

let uu____7901 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (uu____7901) with
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
| uu____7914 -> begin
(

let uu____7915 = (let _0_645 = (let _0_644 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _0_644))
in (tc_check_tot_or_gtot_term (

let uu___130_7919 = env0
in {FStar_TypeChecker_Env.solver = uu___130_7919.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___130_7919.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___130_7919.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___130_7919.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___130_7919.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___130_7919.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___130_7919.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___130_7919.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___130_7919.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___130_7919.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___130_7919.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___130_7919.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___130_7919.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___130_7919.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___130_7919.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___130_7919.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___130_7919.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___130_7919.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___130_7919.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___130_7919.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___130_7919.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___130_7919.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___130_7919.FStar_TypeChecker_Env.qname_and_index}) t _0_645))
in (match (uu____7915) with
| (t, uu____7923, g) -> begin
(

let g = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((let _0_646 = (FStar_TypeChecker_Rel.discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _0_646));
(norm env0 t);
))
end))
end)
in (

let env = (

let uu____7928 = ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env))
in (match (uu____7928) with
| true -> begin
(

let uu___131_7929 = env
in {FStar_TypeChecker_Env.solver = uu___131_7929.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___131_7929.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___131_7929.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___131_7929.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___131_7929.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___131_7929.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___131_7929.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___131_7929.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___131_7929.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___131_7929.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___131_7929.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___131_7929.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___131_7929.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___131_7929.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___131_7929.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___131_7929.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___131_7929.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___131_7929.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___131_7929.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___131_7929.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___131_7929.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___131_7929.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___131_7929.FStar_TypeChecker_Env.qname_and_index})
end
| uu____7936 -> begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end))
in (

let lb = (

let uu___132_7939 = lb
in {FStar_Syntax_Syntax.lbname = uu___132_7939.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___132_7939.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____7882) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____7953 = (let _0_648 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____7972 = (let _0_647 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _0_647 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____7972) with
| (e, c, g) -> begin
((

let uu____7982 = (not ((FStar_Syntax_Util.is_total_lcomp c)))
in (match (uu____7982) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7983 -> begin
()
end));
(

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g)));
)
end)))))
in (FStar_All.pipe_right _0_648 FStar_List.unzip))
in (match (uu____7953) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____8004 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8004) with
| (env1, uu____8014) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____8020 = (check_lbtyp top_level env lb)
in (match (uu____8020) with
| (topt, wf_annot, univ_vars, univ_opening, env1) -> begin
((match (((not (top_level)) && (univ_vars <> []))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____8043 -> begin
()
end);
(

let e1 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____8046 = (tc_maybe_toplevel_term (

let uu___133_8050 = env1
in {FStar_TypeChecker_Env.solver = uu___133_8050.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___133_8050.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___133_8050.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___133_8050.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___133_8050.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___133_8050.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___133_8050.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___133_8050.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___133_8050.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___133_8050.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___133_8050.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___133_8050.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___133_8050.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___133_8050.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___133_8050.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___133_8050.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___133_8050.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___133_8050.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___133_8050.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___133_8050.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___133_8050.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___133_8050.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___133_8050.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (uu____8046) with
| (e1, c1, g1) -> begin
(

let uu____8059 = (let _0_649 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____8064 -> FStar_TypeChecker_Err.ill_kinded_type))) _0_649 e1 c1 wf_annot))
in (match (uu____8059) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____8074 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____8074) with
| true -> begin
(let _0_652 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _0_651 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (let _0_650 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" _0_652 _0_651 _0_650))))
end
| uu____8075 -> begin
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
| uu____8096 -> begin
()
end);
((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____8100 -> begin
(

let uu____8101 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____8101) with
| (univ_opening, univ_vars) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(let _0_653 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (univ_opening), (_0_653)))
end
| uu____8131 -> begin
(

let uu____8132 = (FStar_Syntax_Util.type_u ())
in (match (uu____8132) with
| (k, uu____8143) -> begin
(

let uu____8144 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____8144) with
| (t, uu____8156, g) -> begin
((

let uu____8159 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8159) with
| true -> begin
(let _0_655 = (FStar_Range.string_of_range (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname))
in (let _0_654 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _0_655 _0_654)))
end
| uu____8160 -> begin
()
end));
(

let t = (norm env1 t)
in (let _0_656 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (univ_opening), (_0_656))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____8166 -> (match (uu____8166) with
| (x, imp) -> begin
(

let uu____8177 = (FStar_Syntax_Util.type_u ())
in (match (uu____8177) with
| (tu, u) -> begin
((

let uu____8189 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____8189) with
| true -> begin
(let _0_659 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_658 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _0_657 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _0_659 _0_658 _0_657))))
end
| uu____8190 -> begin
()
end));
(

let uu____8191 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____8191) with
| (t, uu____8202, g) -> begin
(

let x = (((

let uu___134_8207 = x
in {FStar_Syntax_Syntax.ppname = uu___134_8207.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___134_8207.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____8209 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8209) with
| true -> begin
(let _0_661 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _0_660 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _0_661 _0_660)))
end
| uu____8210 -> begin
()
end));
(let _0_662 = (push_binding env x)
in ((x), (_0_662), (g), (u)));
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

let uu____8261 = (tc_binder env b)
in (match (uu____8261) with
| (b, env', g, u) -> begin
(

let uu____8284 = (aux env' bs)
in (match (uu____8284) with
| (bs, env', g', us) -> begin
(let _0_664 = (let _0_663 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _0_663))
in (((b)::bs), (env'), (_0_664), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun uu____8358 uu____8359 -> (match (((uu____8358), (uu____8359))) with
| ((t, imp), (args, g)) -> begin
(

let uu____8396 = (tc_term env t)
in (match (uu____8396) with
| (t, uu____8406, g') -> begin
(let _0_665 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_0_665)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____8428 -> (match (uu____8428) with
| (pats, g) -> begin
(

let uu____8454 = (tc_args env p)
in (match (uu____8454) with
| (args, g') -> begin
(let _0_666 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_0_666)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____8493 = (tc_maybe_toplevel_term env e)
in (match (uu____8493) with
| (e, c, g) -> begin
(

let uu____8503 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____8503) with
| true -> begin
((e), (c), (g))
end
| uu____8507 -> begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let c = (norm_c env c)
in (

let uu____8513 = (

let uu____8516 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c))
in (match (uu____8516) with
| true -> begin
(let _0_667 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_0_667), (false)))
end
| uu____8519 -> begin
(let _0_668 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_0_668), (true)))
end))
in (match (uu____8513) with
| (target_comp, allow_ghost) -> begin
(

let uu____8525 = (FStar_TypeChecker_Rel.sub_comp env c target_comp)
in (match (uu____8525) with
| Some (g') -> begin
(let _0_669 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_0_669)))
end
| uu____8531 -> begin
(match (allow_ghost) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_670 = (FStar_TypeChecker_Err.expected_ghost_expression e c)
in ((_0_670), (e.FStar_Syntax_Syntax.pos))))))
end
| uu____8539 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_671 = (FStar_TypeChecker_Err.expected_pure_expression e c)
in ((_0_671), (e.FStar_Syntax_Syntax.pos))))))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____8552 = (tc_tot_or_gtot_term env t)
in (match (uu____8552) with
| (t, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____8572 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____8572) with
| true -> begin
(let _0_672 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _0_672))
end
| uu____8573 -> begin
()
end));
(

let env = (

let uu___135_8575 = env
in {FStar_TypeChecker_Env.solver = uu___135_8575.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___135_8575.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___135_8575.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___135_8575.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___135_8575.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___135_8575.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___135_8575.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___135_8575.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___135_8575.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___135_8575.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___135_8575.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___135_8575.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___135_8575.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___135_8575.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___135_8575.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___135_8575.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___135_8575.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___135_8575.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___135_8575.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___135_8575.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___135_8575.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___135_8575.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___135_8575.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____8576 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Errors.Error (msg, uu____8592) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_673 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_0_673))))))
end
in (match (uu____8576) with
| (t, c, g) -> begin
(

let uu____8602 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____8602) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____8608 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_676 = (let _0_674 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _0_674))
in (let _0_675 = (FStar_TypeChecker_Env.get_range env)
in ((_0_676), (_0_675)))))))
end))
end)));
))


let universe_or_type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun env e -> ((

let uu____8621 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____8621) with
| true -> begin
(let _0_677 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "<start> universe_of %s\n" _0_677))
end
| uu____8622 -> begin
()
end));
(

let uu____8623 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8623) with
| (env, uu____8630) -> begin
(

let env = (

let uu___138_8634 = env
in {FStar_TypeChecker_Env.solver = uu___138_8634.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___138_8634.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___138_8634.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___138_8634.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___138_8634.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___138_8634.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___138_8634.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___138_8634.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___138_8634.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___138_8634.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___138_8634.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___138_8634.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___138_8634.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___138_8634.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___138_8634.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___138_8634.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___138_8634.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___138_8634.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___138_8634.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___138_8634.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___138_8634.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> FStar_Util.Inl (t))
in (

let ok = (fun u -> ((

let uu____8651 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____8651) with
| true -> begin
(let _0_680 = (FStar_Syntax_Print.tag_of_term e)
in (let _0_679 = (FStar_Syntax_Print.term_to_string e)
in (let _0_678 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print3 "<end> universe_of (%s) %s is %s\n" _0_680 _0_679 _0_678))))
end
| uu____8652 -> begin
()
end));
FStar_Util.Inr (u);
))
in (

let universe_of_type = (fun e t -> (

let uu____8662 = (FStar_Syntax_Util.unrefine t).FStar_Syntax_Syntax.n
in (match (uu____8662) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| uu____8666 -> begin
(fail e t)
end)))
in (

let uu____8667 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____8667) with
| (head, args) -> begin
(

let uu____8695 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____8695) with
| FStar_Syntax_Syntax.Tm_uvar (uu____8698, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____8713 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____8713) with
| FStar_Syntax_Syntax.Tm_arrow (uu____8716, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| uu____8728 -> begin
(universe_of_type e t)
end)))
end
| uu____8729 -> begin
(

let t = (

let uu____8733 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (match (uu____8733) with
| (None) | (Some (FStar_Syntax_Syntax.Tm_unknown)) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____8741 = (tc_term env e)
in (match (uu____8741) with
| (uu____8747, {FStar_Syntax_Syntax.eff_name = uu____8748; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____8750; FStar_Syntax_Syntax.comp = uu____8751}, g) -> begin
((let _0_681 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right _0_681 Prims.ignore));
t;
)
end)))
end
| Some (t) -> begin
((FStar_Syntax_Syntax.mk t) None e.FStar_Syntax_Syntax.pos)
end))
in (let _0_682 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _0_682)))
end))
end))))))
end));
))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____8778 = (universe_or_type_of env e)
in (match (uu____8778) with
| FStar_Util.Inl (t) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_686 = (let _0_684 = (FStar_Syntax_Print.term_to_string e)
in (let _0_683 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _0_684 _0_683)))
in (let _0_685 = (FStar_TypeChecker_Env.get_range env)
in ((_0_686), (_0_685)))))))
end
| FStar_Util.Inr (u) -> begin
u
end)))




