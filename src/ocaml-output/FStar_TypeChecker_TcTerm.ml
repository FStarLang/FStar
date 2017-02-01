
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
in ((let _0_238 = (let _0_237 = (FStar_Syntax_Syntax.as_arg v)
in (let _0_236 = (let _0_235 = (FStar_Syntax_Syntax.as_arg tl)
in (_0_235)::[])
in (_0_237)::_0_236))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _0_238)) (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun uu___76_41 -> (match (uu___76_41) with
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
(let _0_239 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _0_239))
end
| Some (head) -> begin
(let _0_241 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_240 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _0_241 _0_240)))
end)
in (Prims.raise (FStar_Errors.Error ((let _0_242 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_0_242))))))))
in (

let s = (let _0_244 = (let _0_243 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _0_243))
in (FStar_TypeChecker_Util.new_uvar env _0_244))
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

let uu___84_163 = lc
in {FStar_Syntax_Syntax.eff_name = uu___84_163.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___84_163.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____164 -> (let _0_245 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _0_245 t)))}))


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
(let _0_246 = (memo_tk e t)
in ((_0_246), (lc), (guard)))
end
| Some (t') -> begin
((

let uu____243 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____243) with
| true -> begin
(let _0_248 = (FStar_Syntax_Print.term_to_string t)
in (let _0_247 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _0_248 _0_247)))
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
(let _0_252 = (FStar_Syntax_Print.term_to_string t)
in (let _0_251 = (FStar_Syntax_Print.term_to_string t')
in (let _0_250 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (let _0_249 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" _0_252 _0_251 _0_250 _0_249)))))
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
(FStar_All.pipe_left (fun _0_253 -> Some (_0_253)) (FStar_TypeChecker_Err.subtyping_failed env t t'))
end))
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____286 = (FStar_TypeChecker_Util.strengthen_precondition msg env e lc g)
in (match (uu____286) with
| (lc, g) -> begin
(let _0_254 = (memo_tk e t')
in ((_0_254), ((set_lcomp_result lc t')), (g)))
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
(let _0_255 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _0_255))
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
(let _0_256 = (norm_c env c)
in ((e), (_0_256), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
((

let uu____379 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____379) with
| true -> begin
(let _0_259 = (FStar_Syntax_Print.term_to_string e)
in (let _0_258 = (FStar_Syntax_Print.comp_to_string c)
in (let _0_257 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _0_259 _0_258 _0_257))))
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
(let _0_262 = (FStar_Syntax_Print.term_to_string e)
in (let _0_261 = (FStar_Syntax_Print.comp_to_string c)
in (let _0_260 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _0_262 _0_261 _0_260))))
end
| uu____384 -> begin
()
end));
(

let uu____385 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (uu____385) with
| (e, uu____393, g) -> begin
(

let g = (let _0_263 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _0_263 "could not prove post-condition" g))
in ((

let uu____397 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____397) with
| true -> begin
(let _0_265 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _0_264 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _0_265 _0_264)))
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
(Prims.raise (FStar_Errors.Error ((let _0_267 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f)
in (let _0_266 = (FStar_TypeChecker_Env.get_range env)
in ((_0_267), (_0_266)))))))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let uu____437 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____437) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _0_268 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _0_268))
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
(let _0_270 = (let _0_269 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _0_269))
in (FStar_Errors.warn t.FStar_Syntax_Syntax.pos _0_270))
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

let uu___85_578 = env
in {FStar_TypeChecker_Env.solver = uu___85_578.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___85_578.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___85_578.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___85_578.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___85_578.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___85_578.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___85_578.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___85_578.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___85_578.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___85_578.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___85_578.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___85_578.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___85_578.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___85_578.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___85_578.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___85_578.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___85_578.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___85_578.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___85_578.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___85_578.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___85_578.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___85_578.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___85_578.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu____601 -> (match (uu____601) with
| (b, uu____606) -> begin
(

let t = (let _0_271 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _0_271))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| uu____611 -> begin
(let _0_272 = (FStar_Syntax_Syntax.bv_to_name b)
in (_0_272)::[])
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

let uu____646 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___77_650 -> (match (uu___77_650) with
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
(let _0_274 = (let _0_273 = Some ((FStar_Syntax_Syntax.range_of_bv x))
in (FStar_Syntax_Syntax.new_bv _0_273 x.FStar_Syntax_Syntax.sort))
in ((_0_274), (imp)))
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

let precedes = ((let _0_278 = (let _0_277 = (FStar_Syntax_Syntax.as_arg dec)
in (let _0_276 = (let _0_275 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_0_275)::[])
in (_0_277)::_0_276))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _0_278)) None r)
in (

let uu____744 = (FStar_Util.prefix formals)
in (match (uu____744) with
| (bs, (last, imp)) -> begin
(

let last = (

let uu___86_770 = last
in (let _0_279 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = uu___86_770.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___86_770.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_279}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in ((

let uu____785 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____785) with
| true -> begin
(let _0_282 = (FStar_Syntax_Print.lbname_to_string l)
in (let _0_281 = (FStar_Syntax_Print.term_to_string t)
in (let _0_280 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _0_282 _0_281 _0_280))))
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

let uu___87_1053 = env
in {FStar_TypeChecker_Env.solver = uu___87_1053.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___87_1053.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___87_1053.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___87_1053.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___87_1053.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___87_1053.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___87_1053.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___87_1053.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___87_1053.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___87_1053.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___87_1053.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___87_1053.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___87_1053.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___87_1053.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___87_1053.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___87_1053.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___87_1053.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___87_1053.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___87_1053.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___87_1053.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___87_1053.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___87_1053.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___87_1053.FStar_TypeChecker_Env.qname_and_index}) e))
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
(let _0_285 = (let _0_283 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _0_283))
in (let _0_284 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _0_285 _0_284)))
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

let uu___88_1118 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___88_1118.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___88_1118.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___88_1118.FStar_TypeChecker_Env.implicits})
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

let uu___89_1192 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___89_1192.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___89_1192.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___89_1192.FStar_TypeChecker_Env.implicits})
in (let _0_287 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats)))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _0_286 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_0_287), (c), (_0_286)))))
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

let uu____1238 = (let _0_288 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _0_288 e1))
in (match (uu____1238) with
| (e1, c1, g1) -> begin
(

let uu____1248 = (tc_term env e2)
in (match (uu____1248) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_291 = (let _0_290 = (let _0_289 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_0_289)::[])
in ((false), (_0_290)))
in ((_0_291), (e2)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _0_292 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_0_292)))))))
end))
end))
end
| uu____1294 -> begin
(

let uu____1295 = (tc_term env e)
in (match (uu____1295) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____1319)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let uu____1334 = (tc_term env e)
in (match (uu____1334) with
| (e, c, g) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), uu____1359) -> begin
(

let uu____1378 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1378) with
| (env0, uu____1386) -> begin
(

let uu____1389 = (tc_comp env0 expected_c)
in (match (uu____1389) with
| (expected_c, uu____1397, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let uu____1402 = (let _0_293 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _0_293 e))
in (match (uu____1402) with
| (e, c', g') -> begin
(

let uu____1412 = (let _0_295 = (let _0_294 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_0_294)))
in (check_expected_effect env0 (Some (expected_c)) _0_295))
in (match (uu____1412) with
| (e, expected_c, g'') -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c))))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (let _0_296 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _0_296))
in (

let uu____1448 = (comp_check_expected_typ env e lc)
in (match (uu____1448) with
| (e, c, f2) -> begin
(let _0_297 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (_0_297)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), uu____1460) -> begin
(

let uu____1479 = (FStar_Syntax_Util.type_u ())
in (match (uu____1479) with
| (k, u) -> begin
(

let uu____1487 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____1487) with
| (t, uu____1495, f) -> begin
(

let uu____1497 = (let _0_298 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _0_298 e))
in (match (uu____1497) with
| (e, c, g) -> begin
(

let uu____1507 = (let _0_299 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____1512 -> FStar_TypeChecker_Err.ill_kinded_type))) _0_299 e c f))
in (match (uu____1507) with
| (c, f) -> begin
(

let uu____1518 = (let _0_300 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name)))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _0_300 c))
in (match (uu____1518) with
| (e, c, f2) -> begin
(let _0_302 = (let _0_301 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _0_301))
in ((e), (c), (_0_302)))
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

let uu____1623 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1623) with
| (unary_op, uu____1637) -> begin
(

let head = (let _0_303 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[]))))) None _0_303))
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest))))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____1698; FStar_Syntax_Syntax.pos = uu____1699; FStar_Syntax_Syntax.vars = uu____1700}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____1725 -> begin
()
end);
(

let uu____1726 = (

let uu____1730 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1730) with
| (env0, uu____1738) -> begin
(tc_term env0 e)
end))
in (match (uu____1726) with
| (e, c, g) -> begin
(

let uu____1747 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1747) with
| (reify_op, uu____1761) -> begin
(

let u_c = (

let uu____1777 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (uu____1777) with
| (uu____1781, c', uu____1783) -> begin
(

let uu____1784 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n
in (match (uu____1784) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____1786 -> begin
(

let uu____1787 = (FStar_Syntax_Util.type_u ())
in (match (uu____1787) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq env c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g')
end
| None -> begin
(failwith (let _0_306 = (FStar_Syntax_Print.lcomp_to_string c')
in (let _0_305 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (let _0_304 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" _0_306 _0_305 _0_304)))))
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

let c = (let _0_307 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _0_307 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____1818 = (comp_check_expected_typ env e c)
in (match (uu____1818) with
| (e, c, g') -> begin
(let _0_308 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_0_308)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = uu____1829; FStar_Syntax_Syntax.pos = uu____1830; FStar_Syntax_Syntax.vars = uu____1831}, ((e, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____1856 -> begin
()
end);
(

let no_reflect = (fun uu____1863 -> (Prims.raise (FStar_Errors.Error ((let _0_309 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_0_309), (e.FStar_Syntax_Syntax.pos)))))))
in (

let uu____1867 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1867) with
| (reflect_op, uu____1881) -> begin
(

let uu____1896 = (FStar_TypeChecker_Env.effect_decl_opt env l)
in (match (uu____1896) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
(

let uu____1902 = (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers FStar_Syntax_Syntax.contains_reflectable)))
in (match (uu____1902) with
| true -> begin
(no_reflect ())
end
| uu____1907 -> begin
(

let uu____1908 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1908) with
| (env_no_ex, topt) -> begin
(

let uu____1919 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_313 = (let _0_312 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _0_311 = (let _0_310 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_0_310)::[])
in (_0_312)::_0_311))
in ((repr), (_0_313)))))) None top.FStar_Syntax_Syntax.pos)
in (

let uu____1943 = (let _0_315 = (let _0_314 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _0_314 Prims.fst))
in (tc_tot_or_gtot_term _0_315 t))
in (match (uu____1943) with
| (t, uu____1960, g) -> begin
(

let uu____1962 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1962) with
| FStar_Syntax_Syntax.Tm_app (uu____1971, ((res, uu____1973))::((wp, uu____1975))::[]) -> begin
((t), (res), (wp), (g))
end
| uu____2009 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____1919) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____2033 = (

let uu____2036 = (tc_tot_or_gtot_term env_no_ex e)
in (match (uu____2036) with
| (e, c, g) -> begin
((

let uu____2046 = (let _0_316 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _0_316))
in (match (uu____2046) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____2051 -> begin
()
end));
(

let uu____2052 = (FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____2052) with
| None -> begin
((let _0_321 = (let _0_320 = (let _0_319 = (let _0_318 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _0_317 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _0_318 _0_317)))
in ((_0_319), (e.FStar_Syntax_Syntax.pos)))
in (_0_320)::[])
in (FStar_TypeChecker_Err.add_errors env _0_321));
(let _0_322 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_0_322)));
)
end
| Some (g') -> begin
(let _0_324 = (let _0_323 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _0_323))
in ((e), (_0_324)))
end));
)
end))
in (match (uu____2033) with
| (e, g) -> begin
(

let c = (let _0_329 = (FStar_Syntax_Syntax.mk_Comp (let _0_328 = (let _0_325 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (_0_325)::[])
in (let _0_327 = (let _0_326 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_326)::[])
in {FStar_Syntax_Syntax.comp_univs = _0_328; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _0_327; FStar_Syntax_Syntax.flags = []})))
in (FStar_All.pipe_right _0_329 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[]))))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____2088 = (comp_check_expected_typ env e c)
in (match (uu____2088) with
| (e, c, g') -> begin
(let _0_330 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_0_330)))
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

let env = (let _0_332 = (let _0_331 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _0_331 Prims.fst))
in (FStar_All.pipe_right _0_332 instantiate_both))
in ((

let uu____2121 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____2121) with
| true -> begin
(let _0_334 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _0_333 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _0_334 _0_333)))
end
| uu____2122 -> begin
()
end));
(

let uu____2123 = (tc_term (no_inst env) head)
in (match (uu____2123) with
| (head, chead, g_head) -> begin
(

let uu____2133 = (

let uu____2137 = ((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head))
in (match (uu____2137) with
| true -> begin
(let _0_335 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _0_335))
end
| uu____2141 -> begin
(let _0_336 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _0_336))
end))
in (match (uu____2133) with
| (e, c, g) -> begin
((

let uu____2149 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2149) with
| true -> begin
(let _0_337 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _0_337))
end
| uu____2150 -> begin
()
end));
(

let c = (

let uu____2152 = (((FStar_TypeChecker_Env.should_verify env) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____2152) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end
| uu____2153 -> begin
c
end))
in (

let uu____2154 = (comp_check_expected_typ env0 e c)
in (match (uu____2154) with
| (e, c, g') -> begin
(

let gimp = (

let uu____2165 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____2165) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____2167) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let uu___90_2199 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___90_2199.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___90_2199.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___90_2199.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____2224 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (let _0_338 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _0_338))
in ((

let uu____2227 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2227) with
| true -> begin
(let _0_340 = (FStar_Syntax_Print.term_to_string e)
in (let _0_339 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _0_340 _0_339)))
end
| uu____2228 -> begin
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

let uu____2257 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2257) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let uu____2269 = (tc_term env1 e1)
in (match (uu____2269) with
| (e1, c1, g1) -> begin
(

let uu____2279 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let uu____2285 = (FStar_Syntax_Util.type_u ())
in (match (uu____2285) with
| (k, uu____2291) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _0_341 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_0_341), (res_t))))
end))
end)
in (match (uu____2279) with
| (env_branches, res_t) -> begin
((

let uu____2299 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2299) with
| true -> begin
(let _0_342 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" _0_342))
end
| uu____2300 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____2350 = (

let uu____2353 = (FStar_List.fold_right (fun uu____2372 uu____2373 -> (match (((uu____2372), (uu____2373))) with
| ((uu____2405, f, c, g), (caccum, gaccum)) -> begin
(let _0_343 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_0_343)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____2353) with
| (cases, g) -> begin
(let _0_344 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_0_344), (g)))
end))
in (match (uu____2350) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____2510 -> (match (uu____2510) with
| ((pat, wopt, br), uu____2526, lc, uu____2528) -> begin
(let _0_345 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (_0_345)))
end))))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name)))))) None e.FStar_Syntax_Syntax.pos)))))
in (

let uu____2574 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____2574) with
| true -> begin
(mk_match e1)
end
| uu____2577 -> begin
(

let e_match = (mk_match (FStar_Syntax_Syntax.bv_to_name guard_x))
in (

let lb = (let _0_346 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _0_346; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_349 = (let _0_348 = (let _0_347 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_0_347)::[])
in (FStar_Syntax_Subst.close _0_348 e_match))
in ((((false), ((lb)::[]))), (_0_349)))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____2598 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2598) with
| true -> begin
(let _0_352 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _0_351 = (let _0_350 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _0_350))
in (FStar_Util.print2 "(%s) comp type = %s\n" _0_352 _0_351)))
end
| uu____2599 -> begin
()
end));
(let _0_353 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_0_353)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2602); FStar_Syntax_Syntax.lbunivs = uu____2603; FStar_Syntax_Syntax.lbtyp = uu____2604; FStar_Syntax_Syntax.lbeff = uu____2605; FStar_Syntax_Syntax.lbdef = uu____2606})::[]), uu____2607) -> begin
((

let uu____2622 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2622) with
| true -> begin
(let _0_354 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _0_354))
end
| uu____2623 -> begin
()
end));
(check_top_level_let env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____2624), uu____2625) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____2635); FStar_Syntax_Syntax.lbunivs = uu____2636; FStar_Syntax_Syntax.lbtyp = uu____2637; FStar_Syntax_Syntax.lbeff = uu____2638; FStar_Syntax_Syntax.lbdef = uu____2639})::uu____2640), uu____2641) -> begin
((

let uu____2657 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2657) with
| true -> begin
(let _0_355 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _0_355))
end
| uu____2658 -> begin
()
end));
(check_top_level_let_rec env top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____2659), uu____2660) -> begin
(check_inner_let_rec env top)
end));
)))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let uu____2704 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____2704) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____2717 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2717) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____2720 -> begin
FStar_Util.Inr ((let _0_356 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_356)))
end))
in (

let is_data_ctor = (fun uu___78_2727 -> (match (uu___78_2727) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| uu____2730 -> begin
false
end))
in (

let uu____2732 = ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v))))
in (match (uu____2732) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_358 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _0_357 = (FStar_TypeChecker_Env.get_range env)
in ((_0_358), (_0_357)))))))
end
| uu____2743 -> begin
(value_check_expected_typ env e tc implicits)
end))))
end)))
in (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(failwith (let _0_359 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _0_359)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____2768 = (FStar_Syntax_Subst.compress t1).FStar_Syntax_Syntax.n
in (match (uu____2768) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2769) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____2777 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___91_2797 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___91_2797.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___91_2797.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___91_2797.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____2825 = (

let uu____2832 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____2832) with
| None -> begin
(

let uu____2840 = (FStar_Syntax_Util.type_u ())
in (match (uu____2840) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____2825) with
| (t, uu____2861, g0) -> begin
(

let uu____2869 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (uu____2869) with
| (e, uu____2880, g1) -> begin
(let _0_362 = (let _0_360 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _0_360 FStar_Syntax_Util.lcomp_of_comp))
in (let _0_361 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_0_362), (_0_361))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (match (env.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____2894 -> begin
(FStar_TypeChecker_Env.lookup_bv env x)
end)
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let uu___92_2896 = x
in {FStar_Syntax_Syntax.ppname = uu___92_2896.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___92_2896.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let uu____2897 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (uu____2897) with
| (e, t, implicits) -> begin
(

let tc = (

let uu____2910 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2910) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____2913 -> begin
FStar_Util.Inr ((let _0_363 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_363)))
end))
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____2917; FStar_Syntax_Syntax.pos = uu____2918; FStar_Syntax_Syntax.vars = uu____2919}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let uu____2927 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2927) with
| (us', t) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_364 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_0_364))))))
end
| uu____2944 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____2951 -> begin
(failwith "Impossible")
end)) us' us)
end);
(

let fv' = (

let uu___93_2953 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___94_2954 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___94_2954.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___94_2954.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___93_2953.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___93_2953.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _0_365 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_365 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2987 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2987) with
| (us, t) -> begin
((

let uu____3000 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Range")))
in (match (uu____3000) with
| true -> begin
(let _0_370 = (FStar_Syntax_Print.lid_to_string (FStar_Syntax_Syntax.lid_of_fv fv))
in (let _0_369 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _0_368 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid (FStar_Syntax_Syntax.lid_of_fv fv)))
in (let _0_367 = (FStar_Range.string_of_use_range (FStar_Ident.range_of_lid (FStar_Syntax_Syntax.lid_of_fv fv)))
in (let _0_366 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s" _0_370 _0_369 _0_368 _0_367 _0_366))))))
end
| uu____3001 -> begin
()
end));
(

let fv' = (

let uu___95_3003 = fv
in {FStar_Syntax_Syntax.fv_name = (

let uu___96_3004 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = uu___96_3004.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = uu___96_3004.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = uu___95_3003.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu___95_3003.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _0_371 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv'))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_371 us))
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

let uu____3061 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3061) with
| (bs, c) -> begin
(

let env0 = env
in (

let uu____3070 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3070) with
| (env, uu____3078) -> begin
(

let uu____3081 = (tc_binders env bs)
in (match (uu____3081) with
| (bs, env, g, us) -> begin
(

let uu____3093 = (tc_comp env c)
in (match (uu____3093) with
| (c, uc, f) -> begin
(

let e = (

let uu___97_3106 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = uu___97_3106.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___97_3106.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___97_3106.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env e bs c);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _0_372 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _0_372))
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

let uu____3161 = (let _0_374 = (let _0_373 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_373)::[])
in (FStar_Syntax_Subst.open_term _0_374 phi))
in (match (uu____3161) with
| (x, phi) -> begin
(

let env0 = env
in (

let uu____3170 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3170) with
| (env, uu____3178) -> begin
(

let uu____3181 = (let _0_375 = (FStar_List.hd x)
in (tc_binder env _0_375))
in (match (uu____3181) with
| (x, env, f1, u) -> begin
((

let uu____3202 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____3202) with
| true -> begin
(let _0_378 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _0_377 = (FStar_Syntax_Print.term_to_string phi)
in (let _0_376 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _0_378 _0_377 _0_376))))
end
| uu____3203 -> begin
()
end));
(

let uu____3204 = (FStar_Syntax_Util.type_u ())
in (match (uu____3204) with
| (t_phi, uu____3211) -> begin
(

let uu____3212 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (uu____3212) with
| (phi, uu____3220, f2) -> begin
(

let e = (

let uu___98_3225 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = uu___98_3225.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___98_3225.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___98_3225.FStar_Syntax_Syntax.vars})
in (

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _0_379 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _0_379))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____3252) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in ((

let uu____3277 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3277) with
| true -> begin
(let _0_380 = (FStar_Syntax_Print.term_to_string (

let uu___99_3278 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = uu___99_3278.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___99_3278.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___99_3278.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _0_380))
end
| uu____3296 -> begin
()
end));
(

let uu____3297 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3297) with
| (bs, body) -> begin
(tc_abs env top bs body)
end));
))
end
| uu____3305 -> begin
(failwith (let _0_382 = (FStar_Syntax_Print.term_to_string top)
in (let _0_381 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _0_382 _0_381))))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (uu____3311) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (uu____3312, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (uu____3318, Some (uu____3319)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____3327) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (uu____3331) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (uu____3332) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____3333) -> begin
FStar_TypeChecker_Common.t_range
end
| uu____3334 -> begin
(Prims.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____3345) -> begin
(

let uu____3352 = (FStar_Syntax_Util.type_u ())
in (match (uu____3352) with
| (k, u) -> begin
(

let uu____3360 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3360) with
| (t, uu____3368, g) -> begin
(let _0_383 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((_0_383), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____3371) -> begin
(

let uu____3378 = (FStar_Syntax_Util.type_u ())
in (match (uu____3378) with
| (k, u) -> begin
(

let uu____3386 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____3386) with
| (t, uu____3394, g) -> begin
(let _0_384 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((_0_384), (u), (g)))
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

let tc = ((let _0_386 = (let _0_385 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_0_385)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _0_386)) None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos)
in (

let uu____3415 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____3415) with
| (tc, uu____3423, f) -> begin
(

let uu____3425 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3425) with
| (head, args) -> begin
(

let comp_univs = (

let uu____3455 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____3455) with
| FStar_Syntax_Syntax.Tm_uinst (uu____3456, us) -> begin
us
end
| uu____3462 -> begin
[]
end))
in (

let uu____3463 = (FStar_Syntax_Util.head_and_args tc)
in (match (uu____3463) with
| (uu____3476, args) -> begin
(

let uu____3492 = (let _0_388 = (FStar_List.hd args)
in (let _0_387 = (FStar_List.tl args)
in ((_0_388), (_0_387))))
in (match (uu____3492) with
| (res, args) -> begin
(

let uu____3544 = (let _0_389 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___79_3562 -> (match (uu___79_3562) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____3568 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3568) with
| (env, uu____3575) -> begin
(

let uu____3578 = (tc_tot_or_gtot_term env e)
in (match (uu____3578) with
| (e, uu____3585, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _0_389 FStar_List.unzip))
in (match (uu____3544) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let uu___100_3601 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___100_3601.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = uu___100_3601.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____3605 = (FStar_TypeChecker_Util.effect_repr env c u)
in (match (uu____3605) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (let _0_390 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_0_390))))))
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
| FStar_Syntax_Syntax.U_bvar (uu____3615) -> begin
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
| uu____3621 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _0_391 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_391 Prims.snd))
end
| uu____3624 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (Prims.raise (FStar_Errors.Error ((let _0_392 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_0_392), (top.FStar_Syntax_Syntax.pos)))))))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun uu____3702 bs bs_expected -> (match (uu____3702) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
((match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_395 = (let _0_393 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _0_393))
in (let _0_394 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_0_395), (_0_394)))))))
end
| uu____3799 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____3803 = (

let uu____3806 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
in (match (uu____3806) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____3809 -> begin
((

let uu____3811 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____3811) with
| true -> begin
(let _0_396 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _0_396))
end
| uu____3812 -> begin
()
end));
(

let uu____3813 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (uu____3813) with
| (t, uu____3820, g1) -> begin
(

let g2 = (let _0_398 = (FStar_TypeChecker_Env.get_range env)
in (let _0_397 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _0_398 "Type annotation on parameter incompatible with the expected type" _0_397)))
in (

let g = (let _0_399 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _0_399))
in ((t), (g))))
end));
)
end))
in (match (uu____3803) with
| (t, g) -> begin
(

let hd = (

let uu___101_3839 = hd
in {FStar_Syntax_Syntax.ppname = uu___101_3839.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___101_3839.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _0_400 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _0_400))
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
| uu____3941 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____3945 = (tc_binders env bs)
in (match (uu____3945) with
| (bs, envbody, g, uu____3964) -> begin
(

let uu____3965 = (

let uu____3970 = (FStar_Syntax_Subst.compress body).FStar_Syntax_Syntax.n
in (match (uu____3970) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), uu____3977) -> begin
(

let uu____3996 = (tc_comp envbody c)
in (match (uu____3996) with
| (c, uu____4005, g') -> begin
(let _0_401 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_0_401)))
end))
end
| uu____4008 -> begin
((None), (body), (g))
end))
in (match (uu____3965) with
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

let uu____4058 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____4058) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
((match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4087 -> begin
(failwith "Impossible")
end);
(

let uu____4091 = (tc_binders env bs)
in (match (uu____4091) with
| (bs, envbody, g, uu____4111) -> begin
(

let uu____4112 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____4112) with
| (envbody, uu____4129) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____4140) -> begin
(

let uu____4145 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (uu____4145) with
| (uu____4170, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____4206 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____4206) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun uu____4267 c_expected -> (match (uu____4267) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _0_402 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_0_402)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.arrow more_bs_expected c_expected))
in (let _0_403 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_0_403))))
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

let uu____4384 = (check_binders env more_bs bs_expected)
in (match (uu____4384) with
| (env, bs', more, guard', subst) -> begin
(let _0_405 = (let _0_404 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_0_404), (subst)))
in (handle_more _0_405 c_expected))
end))
end
| uu____4432 -> begin
(let _0_407 = (let _0_406 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _0_406))
in (fail _0_407 t))
end))
end
| uu____4440 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end))
end)
end))
in (let _0_408 = (check_binders env bs bs_expected)
in (handle_more _0_408 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let uu___102_4470 = envbody
in {FStar_TypeChecker_Env.solver = uu___102_4470.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___102_4470.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___102_4470.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___102_4470.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___102_4470.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___102_4470.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___102_4470.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___102_4470.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___102_4470.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___102_4470.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___102_4470.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___102_4470.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___102_4470.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___102_4470.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___102_4470.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___102_4470.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___102_4470.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___102_4470.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___102_4470.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___102_4470.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___102_4470.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___102_4470.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___102_4470.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____4484 uu____4485 -> (match (((uu____4484), (uu____4485))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let uu____4510 = (let _0_410 = (let _0_409 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _0_409 Prims.fst))
in (tc_term _0_410 t))
in (match (uu____4510) with
| (t, uu____4522, uu____4523) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _0_411 = (FStar_Syntax_Syntax.mk_binder (

let uu___103_4530 = x
in {FStar_Syntax_Syntax.ppname = uu___103_4530.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___103_4530.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_0_411)::letrec_binders)
end
| uu____4531 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let uu____4534 = (check_actuals_against_formals env bs bs_expected)
in (match (uu____4534) with
| (envbody, bs, g, c) -> begin
(

let uu____4564 = (

let uu____4568 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____4568) with
| true -> begin
(mk_letrec_env envbody bs c)
end
| uu____4572 -> begin
((envbody), ([]))
end))
in (match (uu____4564) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| uu____4601 -> begin
(match ((not (norm))) with
| true -> begin
(let _0_412 = (unfold_whnf env t)
in (as_function_typ true _0_412))
end
| uu____4614 -> begin
(

let uu____4615 = (expected_function_typ env None body)
in (match (uu____4615) with
| (uu____4639, bs, uu____4641, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end)
end)))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____4662 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____4662) with
| (env, topt) -> begin
((

let uu____4674 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____4674) with
| true -> begin
(let _0_413 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _0_413 (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____4676 -> begin
"false"
end)))
end
| uu____4677 -> begin
()
end));
(

let uu____4678 = (expected_function_typ env topt body)
in (match (uu____4678) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let uu____4708 = (tc_term (

let uu___104_4712 = envbody
in {FStar_TypeChecker_Env.solver = uu___104_4712.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___104_4712.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___104_4712.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___104_4712.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___104_4712.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___104_4712.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___104_4712.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___104_4712.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___104_4712.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___104_4712.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___104_4712.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___104_4712.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___104_4712.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___104_4712.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___104_4712.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___104_4712.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___104_4712.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___104_4712.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___104_4712.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___104_4712.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___104_4712.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___104_4712.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (uu____4708) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in ((

let uu____4721 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))
in (match (uu____4721) with
| true -> begin
(let _0_416 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _0_415 = (let _0_414 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _0_414))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _0_416 _0_415)))
end
| uu____4730 -> begin
()
end));
(

let uu____4731 = (let _0_418 = (let _0_417 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_0_417)))
in (check_expected_effect (

let uu___105_4735 = envbody
in {FStar_TypeChecker_Env.solver = uu___105_4735.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___105_4735.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___105_4735.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___105_4735.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___105_4735.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___105_4735.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___105_4735.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___105_4735.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___105_4735.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___105_4735.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___105_4735.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___105_4735.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___105_4735.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___105_4735.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___105_4735.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___105_4735.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___105_4735.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___105_4735.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___105_4735.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___105_4735.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___105_4735.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___105_4735.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___105_4735.FStar_TypeChecker_Env.qname_and_index}) c_opt _0_418))
in (match (uu____4731) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = (

let uu____4746 = (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env))))
in (match (uu____4746) with
| true -> begin
(let _0_419 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _0_419))
end
| uu____4747 -> begin
(

let guard = (let _0_420 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _0_420))
in guard)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _0_423 = Some ((let _0_422 = (FStar_All.pipe_right (FStar_Util.dflt cbody c_opt) FStar_Syntax_Util.lcomp_of_comp)
in (FStar_All.pipe_right _0_422 (fun _0_421 -> FStar_Util.Inl (_0_421)))))
in (FStar_Syntax_Util.abs bs body _0_423))
in (

let uu____4768 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4783) -> begin
((e), (t), (guard))
end
| uu____4791 -> begin
(

let uu____4792 = (match (use_teq) with
| true -> begin
(let _0_424 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_0_424)))
end
| uu____4797 -> begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end)
in (match (uu____4792) with
| (e, guard') -> begin
(let _0_425 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_0_425)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (uu____4768) with
| (e, tfun, guard) -> begin
(

let c = (match (env.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____4814 -> begin
(FStar_TypeChecker_Util.return_value env tfun e)
end)
in (

let uu____4815 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (uu____4815) with
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

let uu____4851 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____4851) with
| true -> begin
(let _0_427 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _0_426 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _0_427 _0_426)))
end
| uu____4852 -> begin
()
end));
(

let monadic_application = (fun uu____4893 subst arg_comps_rev arg_rets guard fvs bs -> (match (uu____4893) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___106_4934 = cres
in {FStar_Syntax_Syntax.eff_name = uu___106_4934.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___106_4934.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___106_4934.FStar_Syntax_Syntax.comp})
in (

let uu____4935 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun uu___80_4962 -> (match (uu___80_4962) with
| (uu____4971, uu____4972, FStar_Util.Inl (uu____4973)) -> begin
false
end
| (uu____4984, uu____4985, FStar_Util.Inr (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = (match (refine_with_equality) with
| true -> begin
(let _0_428 = ((FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets)) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _0_428 cres))
end
| uu____5006 -> begin
((

let uu____5008 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5008) with
| true -> begin
(let _0_431 = (FStar_Syntax_Print.term_to_string head)
in (let _0_430 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _0_429 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _0_431 _0_430 _0_429))))
end
| uu____5009 -> begin
()
end));
cres;
)
end)
in ((cres), (g))))))
end
| uu____5010 -> begin
(

let g = (let _0_432 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _0_432 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _0_436 = (let _0_435 = (FStar_Syntax_Syntax.mk_Total (let _0_434 = (let _0_433 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _0_433))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _0_434)))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_435))
in ((_0_436), (g))))
end)
in (match (uu____4935) with
| (cres, guard) -> begin
((

let uu____5023 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5023) with
| true -> begin
(let _0_437 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _0_437))
end
| uu____5024 -> begin
()
end));
(

let comp = (FStar_List.fold_left (fun out_c uu____5039 -> (match (uu____5039) with
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

let uu____5085 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____5085) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Or))
end
| uu____5087 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args = (FStar_List.fold_left (fun args uu____5101 -> (match (uu____5101) with
| (arg, uu____5113, uu____5114) -> begin
(arg)::args
end)) [] arg_comps_rev)
in (

let app = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_lift env app cres.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ))))
end
| uu____5133 -> begin
(

let uu____5134 = (

let map_fun = (fun uu____5173 -> (match (uu____5173) with
| ((e, q), uu____5197, c0) -> begin
(match (c0) with
| FStar_Util.Inl (uu____5222) -> begin
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
in (let _0_439 = (let _0_438 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_0_438), (q)))
in ((Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e)))), (_0_439)))))
end)
end))
in (

let uu____5282 = (let _0_443 = (let _0_442 = (let _0_441 = (let _0_440 = (FStar_Syntax_Syntax.as_arg head)
in ((_0_440), (None), (FStar_Util.Inr (chead))))
in (_0_441)::arg_comps_rev)
in (FStar_List.map map_fun _0_442))
in (FStar_All.pipe_left FStar_List.split _0_443))
in (match (uu____5282) with
| (lifted_args, reverse_args) -> begin
(let _0_445 = (Prims.fst (FStar_List.hd reverse_args))
in (let _0_444 = (FStar_List.rev (FStar_List.tl reverse_args))
in ((lifted_args), (_0_445), (_0_444))))
end)))
in (match (uu____5134) with
| (lifted_args, head, args) -> begin
(

let app = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_lift env app cres.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
in (

let app = (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___81_5470 -> (match (uu___81_5470) with
| None -> begin
e
end
| Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1)
in (

let letbinding = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_448 = (let _0_447 = (let _0_446 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_446)::[])
in (FStar_Syntax_Subst.close _0_447 e))
in ((((false), ((lb)::[]))), (_0_448)))))) None e.FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp.FStar_Syntax_Syntax.res_typ)))))))) None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app lifted_args)))))
end))
end)
in (

let uu____5545 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (uu____5545) with
| (comp, g) -> begin
((app), (comp), (g))
end))))));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____5603 bs args -> (match (uu____5603) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (uu____5698))))::rest, ((uu____5700, None))::uu____5701) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let uu____5738 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (uu____5738) with
| (varg, uu____5749, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _0_449 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_0_449)))
in (let _0_451 = (let _0_450 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (FStar_Util.Inl (((FStar_Syntax_Const.effect_Tot_lid), (t))))))::outargs), ((arg)::arg_rets), (_0_450), (fvs)))
in (tc_args head_info _0_451 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| uu____5852 -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___107_5859 = x
in {FStar_Syntax_Syntax.ppname = uu___107_5859.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_5859.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____5861 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____5861) with
| true -> begin
(let _0_452 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _0_452))
end
| uu____5862 -> begin
()
end));
(

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let uu___108_5866 = env
in {FStar_TypeChecker_Env.solver = uu___108_5866.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___108_5866.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___108_5866.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___108_5866.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___108_5866.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___108_5866.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___108_5866.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___108_5866.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___108_5866.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___108_5866.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___108_5866.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___108_5866.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___108_5866.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___108_5866.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___108_5866.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___108_5866.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___108_5866.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___108_5866.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___108_5866.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___108_5866.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___108_5866.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___108_5866.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___108_5866.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____5868 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5868) with
| true -> begin
(let _0_455 = (FStar_Syntax_Print.tag_of_term e)
in (let _0_454 = (FStar_Syntax_Print.term_to_string e)
in (let _0_453 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _0_455 _0_454 _0_453))))
end
| uu____5869 -> begin
()
end));
(

let uu____5870 = (tc_term env e)
in (match (uu____5870) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in (

let uu____5886 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____5886) with
| true -> begin
(

let subst = (let _0_456 = (FStar_List.hd bs)
in (maybe_extend_subst subst _0_456 e))
in (tc_args head_info ((subst), ((((arg), (None), (FStar_Util.Inl (((c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ))))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____5945 -> begin
(

let uu____5946 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name)
in (match (uu____5946) with
| true -> begin
(

let subst = (let _0_457 = (FStar_List.hd bs)
in (maybe_extend_subst subst _0_457 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end
| uu____5995 -> begin
(

let uu____5996 = (FStar_Syntax_Syntax.is_null_binder (FStar_List.hd bs))
in (match (uu____5996) with
| true -> begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _0_458 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_458))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end
| uu____6041 -> begin
(let _0_461 = (let _0_460 = (let _0_459 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name x))
in (_0_459)::arg_rets)
in ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), (_0_460), (g), ((x)::fvs)))
in (tc_args head_info _0_461 rest rest'))
end))
end))
end))))
end));
))));
)));
)
end
| (uu____6078, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____6099) -> begin
(

let uu____6129 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (uu____6129) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _0_462 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _0_462 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let uu____6167 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (uu____6167) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in ((

let uu____6181 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6181) with
| true -> begin
(let _0_463 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _0_463))
end
| uu____6182 -> begin
()
end));
(tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args);
))
end))
end
| uu____6211 when (not (norm)) -> begin
(let _0_464 = (unfold_whnf env tres)
in (aux true _0_464))
end
| uu____6212 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_468 = (let _0_466 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _0_465 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _0_466 _0_465)))
in (let _0_467 = (FStar_Syntax_Syntax.argpos arg)
in ((_0_468), (_0_467)))))))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (

let uu____6231 = (FStar_Syntax_Util.unrefine tf).FStar_Syntax_Syntax.n
in (match (uu____6231) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let uu____6305 = (tc_term env e)
in (match (uu____6305) with
| (e, c, g_e) -> begin
(

let uu____6318 = (tc_args env tl)
in (match (uu____6318) with
| (args, comps, g_rest) -> begin
(let _0_469 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_0_469)))
end))
end))
end))
in (

let uu____6350 = (tc_args env args)
in (match (uu____6350) with
| (args, comps, g_args) -> begin
(

let bs = (FStar_Syntax_Util.null_binders_of_tks (FStar_All.pipe_right comps (FStar_List.map (fun uu____6391 -> (match (uu____6391) with
| (uu____6399, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end)))))
in (

let ml_or_tot = (

let uu____6409 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)
in (match (uu____6409) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| uu____6417 -> begin
FStar_Syntax_Util.ml_comp
end))
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(

let uu____6429 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____6429) with
| FStar_Syntax_Syntax.Tm_type (uu____6434) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| uu____6437 -> begin
ml_or_tot
end))
end)
in (

let cres = (let _0_472 = (let _0_471 = (let _0_470 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_470 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _0_471))
in (ml_or_tot _0_472 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____6445 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6445) with
| true -> begin
(let _0_475 = (FStar_Syntax_Print.term_to_string head)
in (let _0_474 = (FStar_Syntax_Print.term_to_string tf)
in (let _0_473 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _0_475 _0_474 _0_473))))
end
| uu____6446 -> begin
()
end));
(let _0_476 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _0_476));
(

let comp = (let _0_477 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____6451 out -> (match (uu____6451) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _0_477))
in (let _0_479 = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _0_478 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_0_479), (comp), (_0_478)))));
))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6482 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6482) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| uu____6525 -> begin
(match ((not (norm))) with
| true -> begin
(let _0_480 = (unfold_whnf env tf)
in (check_function_app true _0_480))
end
| uu____6531 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_481 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((_0_481), (head.FStar_Syntax_Syntax.pos))))))
end)
end)))
in (let _0_483 = (let _0_482 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _0_482))
in (check_function_app false _0_483)))));
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

let uu____6582 = (FStar_List.fold_left2 (fun uu____6595 uu____6596 uu____6597 -> (match (((uu____6595), (uu____6596), (uu____6597))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((aq <> aq')) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____6640 -> begin
()
end);
(

let uu____6641 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____6641) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _0_484 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _0_484 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _0_488 = (let _0_486 = (let _0_485 = (FStar_Syntax_Syntax.as_arg e)
in (_0_485)::[])
in (FStar_List.append seen _0_486))
in (let _0_487 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_0_488), (_0_487), (ghost)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____6582) with
| (args, guard, ghost) -> begin
(

let e = ((FStar_Syntax_Syntax.mk_Tm_app head args) (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = (match (ghost) with
| true -> begin
(let _0_489 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _0_489 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____6686 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____6687 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (uu____6687) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| uu____6699 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let uu____6721 = (FStar_Syntax_Subst.open_branch branch)
in (match (uu____6721) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____6747 = branch
in (match (uu____6747) with
| (cpat, uu____6767, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let uu____6809 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (uu____6809) with
| (pat_bvs, exps, p) -> begin
((

let uu____6831 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6831) with
| true -> begin
(let _0_491 = (FStar_Syntax_Print.pat_to_string p0)
in (let _0_490 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _0_491 _0_490)))
end
| uu____6832 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let uu____6834 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____6834) with
| (env1, uu____6847) -> begin
(

let env1 = (

let uu___109_6851 = env1
in {FStar_TypeChecker_Env.solver = uu___109_6851.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___109_6851.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___109_6851.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___109_6851.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___109_6851.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___109_6851.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___109_6851.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___109_6851.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___109_6851.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___109_6851.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___109_6851.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___109_6851.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___109_6851.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___109_6851.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___109_6851.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___109_6851.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___109_6851.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___109_6851.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___109_6851.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___109_6851.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___109_6851.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___109_6851.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___109_6851.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let uu____6853 = (let _0_507 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> ((

let uu____6873 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6873) with
| true -> begin
(let _0_493 = (FStar_Syntax_Print.term_to_string e)
in (let _0_492 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _0_493 _0_492)))
end
| uu____6874 -> begin
()
end));
(

let uu____6875 = (tc_term env1 e)
in (match (uu____6875) with
| (e, lc, g) -> begin
((

let uu____6885 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6885) with
| true -> begin
(let _0_495 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _0_494 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _0_495 _0_494)))
end
| uu____6886 -> begin
()
end));
(

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let uu____6889 = (let _0_496 = (FStar_TypeChecker_Rel.discharge_guard env (

let uu___110_6890 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___110_6890.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___110_6890.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___110_6890.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _0_496 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _0_498 = (let _0_497 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _0_497 (FStar_List.map (fun uu____6924 -> (match (uu____6924) with
| (u, uu____6929) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _0_498 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____6941 = (let _0_499 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _0_499))
in (match (uu____6941) with
| true -> begin
(

let unresolved = (let _0_500 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _0_500 FStar_Util.set_elements))
in (Prims.raise (FStar_Errors.Error ((let _0_505 = (let _0_504 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _0_503 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _0_502 = (let _0_501 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____6969 -> (match (uu____6969) with
| (u, uu____6977) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _0_501 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _0_504 _0_503 _0_502))))
in ((_0_505), (p.FStar_Syntax_Syntax.p)))))))
end
| uu____6989 -> begin
()
end));
(

let uu____6991 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6991) with
| true -> begin
(let _0_506 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _0_506))
end
| uu____6992 -> begin
()
end));
((e), (e'));
))))))));
)
end));
))))
in (FStar_All.pipe_right _0_507 FStar_List.unzip))
in (match (uu____6853) with
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

let uu____7015 = (let _0_508 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _0_508 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____7015) with
| (scrutinee_env, uu____7031) -> begin
(

let uu____7034 = (tc_pat true pat_t pattern)
in (match (uu____7034) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let uu____7062 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
(

let uu____7077 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____7077) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7084 -> begin
(

let uu____7085 = (let _0_509 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _0_509 e))
in (match (uu____7085) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end))
end)
in (match (uu____7062) with
| (when_clause, g_when) -> begin
(

let uu____7108 = (tc_term pat_env branch_exp)
in (match (uu____7108) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _0_511 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _0_510 -> Some (_0_510)) _0_511))
end)
in (

let uu____7140 = (

let eqs = (

let uu____7148 = (not ((FStar_TypeChecker_Env.should_verify env)))
in (match (uu____7148) with
| true -> begin
None
end
| uu____7154 -> begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| uu____7174 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _0_513 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _0_512 -> Some (_0_512)) _0_513))
end))
end))) None))
end))
in (

let uu____7203 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (uu____7203) with
| (c, g_branch) -> begin
(

let uu____7213 = (match (((eqs), (when_condition))) with
| uu____7224 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _0_515 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _0_514 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_0_515), (_0_514))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = FStar_TypeChecker_Common.NonTrivial ((FStar_Syntax_Util.mk_conj f w))
in (let _0_518 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _0_517 = (let _0_516 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _0_516 g_when))
in ((_0_518), (_0_517))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _0_519 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_0_519), (g_when)))))
end)
in (match (uu____7213) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _0_521 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _0_520 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_0_521), (_0_520), (g_branch)))))
end))
end)))
in (match (uu____7140) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let uu____7310 = (not ((FStar_TypeChecker_Env.should_verify env)))
in (match (uu____7310) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____7311 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> (

let uu____7343 = (let _0_523 = (FStar_List.length (let _0_522 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _0_522)))
in (_0_523 > (Prims.parse_int "1")))
in (match (uu____7343) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____7355 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____7355) with
| None -> begin
[]
end
| uu____7366 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational None)
in (

let disc = ((let _0_525 = (let _0_524 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_0_524)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _0_525)) None scrutinee_tm.FStar_Syntax_Syntax.pos)
in (let _0_526 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_0_526)::[])))
end)))
end
| uu____7382 -> begin
[]
end)))
in (

let fail = (fun uu____7391 -> (failwith (let _0_529 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _0_528 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _0_527 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _0_529 _0_528 _0_527))))))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____7412) -> begin
(head_constructor t)
end
| uu____7418 -> begin
(fail ())
end))
in (

let pat_exp = (let _0_530 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _0_530 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____7436) -> begin
(let _0_535 = ((let _0_534 = (let _0_533 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _0_532 = (let _0_531 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_0_531)::[])
in (_0_533)::_0_532))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _0_534)) None scrutinee_tm.FStar_Syntax_Syntax.pos)
in (_0_535)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in (

let uu____7454 = (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)))
in (match (uu____7454) with
| true -> begin
[]
end
| uu____7460 -> begin
(let _0_536 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _0_536))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in (

let uu____7484 = (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)))
in (match (uu____7484) with
| true -> begin
[]
end
| uu____7490 -> begin
(

let sub_term_guards = (let _0_540 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____7509 -> (match (uu____7509) with
| (ei, uu____7516) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____7526 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____7526) with
| None -> begin
[]
end
| uu____7533 -> begin
(

let sub_term = ((let _0_539 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (let _0_538 = (let _0_537 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_0_537)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_539 _0_538))) None f.FStar_Syntax_Syntax.p)
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right _0_540 FStar_List.flatten))
in (let _0_541 = (discriminate scrutinee_tm f)
in (FStar_List.append _0_541 sub_term_guards)))
end)))
end
| uu____7556 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> (

let uu____7568 = (not ((FStar_TypeChecker_Env.should_verify env)))
in (match (uu____7568) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end
| uu____7569 -> begin
(

let t = (let _0_542 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _0_542))
in (

let uu____7572 = (FStar_Syntax_Util.type_u ())
in (match (uu____7572) with
| (k, uu____7576) -> begin
(

let uu____7577 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____7577) with
| (t, uu____7582, uu____7583) -> begin
t
end))
end)))
end)))
in (

let branch_guard = (let _0_543 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _0_543 FStar_Syntax_Util.mk_disj_l))
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

let uu____7600 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7600) with
| true -> begin
(let _0_544 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _0_544))
end
| uu____7601 -> begin
()
end));
(let _0_545 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_0_545), (branch_guard), (c), (guard)));
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

let uu____7619 = (check_let_bound_def true env lb)
in (match (uu____7619) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let uu____7633 = (match ((annotated && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
((g1), (e1), (univ_vars), (c1))
end
| uu____7642 -> begin
(

let g1 = (let _0_546 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _0_546 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____7645 = (FStar_List.hd (let _0_549 = (let _0_548 = (let _0_547 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_0_547)))
in (_0_548)::[])
in (FStar_TypeChecker_Util.generalize env _0_549)))
in (match (uu____7645) with
| (uu____7676, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end)
in (match (uu____7633) with
| (g1, e1, univ_vars, c1) -> begin
(

let uu____7687 = (

let uu____7692 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____7692) with
| true -> begin
(

let uu____7697 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (uu____7697) with
| (ok, c1) -> begin
(match (ok) with
| true -> begin
((e2), (c1))
end
| uu____7712 -> begin
((

let uu____7714 = (FStar_Options.warn_top_level_effects ())
in (match (uu____7714) with
| true -> begin
(let _0_550 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.warn _0_550 FStar_TypeChecker_Err.top_level_effect))
end
| uu____7715 -> begin
()
end));
(let _0_551 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))))) None e2.FStar_Syntax_Syntax.pos)
in ((_0_551), (c1)));
)
end)
end))
end
| uu____7732 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let c = (let _0_552 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right _0_552 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c)));
)
end))
in (match (uu____7687) with
| (e2, c1) -> begin
(

let cres = (let _0_553 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_553))
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _0_554 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_0_554), (cres), (FStar_TypeChecker_Rel.trivial_guard))));
))
end))
end))
end))
end
| uu____7777 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let uu___111_7798 = env
in {FStar_TypeChecker_Env.solver = uu___111_7798.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_7798.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_7798.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_7798.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_7798.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_7798.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_7798.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_7798.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_7798.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_7798.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_7798.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_7798.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_7798.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___111_7798.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_7798.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_7798.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_7798.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___111_7798.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___111_7798.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___111_7798.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_7798.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_7798.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_7798.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____7799 = (let _0_556 = (let _0_555 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _0_555 Prims.fst))
in (check_let_bound_def false _0_556 lb))
in (match (uu____7799) with
| (e1, uu____7813, c1, g1, annotated) -> begin
(

let x = (

let uu___112_7818 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___112_7818.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_7818.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____7819 = (let _0_558 = (let _0_557 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_557)::[])
in (FStar_Syntax_Subst.open_term _0_558 e2))
in (match (uu____7819) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let uu____7833 = (let _0_559 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _0_559 e2))
in (match (uu____7833) with
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

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_560 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_0_560)))))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _0_563 = (let _0_562 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _0_562 e1))
in (FStar_All.pipe_left (fun _0_561 -> FStar_TypeChecker_Common.NonTrivial (_0_561)) _0_563))
in (

let g2 = (let _0_565 = (let _0_564 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _0_564 g2))
in (FStar_TypeChecker_Rel.close_guard xb _0_565))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (

let uu____7871 = (FStar_Option.isSome (FStar_TypeChecker_Env.expected_typ env))
in (match (uu____7871) with
| true -> begin
(

let tt = (let _0_566 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right _0_566 FStar_Option.get))
in ((

let uu____7878 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____7878) with
| true -> begin
(let _0_568 = (FStar_Syntax_Print.term_to_string tt)
in (let _0_567 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" _0_568 _0_567)))
end
| uu____7879 -> begin
()
end));
((e), (cres), (guard));
))
end
| uu____7880 -> begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____7883 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports")))
in (match (uu____7883) with
| true -> begin
(let _0_570 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (let _0_569 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" _0_570 _0_569)))
end
| uu____7884 -> begin
()
end));
((e), ((

let uu___113_7885 = cres
in {FStar_Syntax_Syntax.eff_name = uu___113_7885.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___113_7885.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___113_7885.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____7886 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____7907 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____7907) with
| (lbs, e2) -> begin
(

let uu____7918 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____7918) with
| (env0, topt) -> begin
(

let uu____7929 = (build_let_rec_env true env0 lbs)
in (match (uu____7929) with
| (lbs, rec_env) -> begin
(

let uu____7940 = (check_let_recs rec_env lbs)
in (match (uu____7940) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _0_571 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _0_571 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _0_573 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _0_573 (fun _0_572 -> Some (_0_572))))
in (

let lbs = (match ((not (env.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (match ((lb.FStar_Syntax_Syntax.lbunivs = [])) with
| true -> begin
lb
end
| uu____7969 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end))))
end
| uu____7970 -> begin
(

let ecs = (let _0_575 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _0_574 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_0_574))))))
in (FStar_TypeChecker_Util.generalize env _0_575))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____8013 -> (match (uu____8013) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (let _0_576 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_576))
in ((FStar_ST.write e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let uu____8044 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____8044) with
| (lbs, e2) -> begin
(let _0_578 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _0_577 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_0_578), (cres), (_0_577))))
end));
)))))
end))
end))
end))
end))
end
| uu____8073 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8094 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8094) with
| (lbs, e2) -> begin
(

let uu____8105 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8105) with
| (env0, topt) -> begin
(

let uu____8116 = (build_let_rec_env false env0 lbs)
in (match (uu____8116) with
| (lbs, rec_env) -> begin
(

let uu____8127 = (check_let_recs rec_env lbs)
in (match (uu____8127) with
| (lbs, g_lbs) -> begin
(

let uu____8138 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let uu___114_8149 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___114_8149.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_8149.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let uu___115_8151 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___115_8151.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___115_8151.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___115_8151.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___115_8151.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (uu____8138) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____8168 = (tc_term env e2)
in (match (uu____8168) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let uu___116_8182 = cres
in {FStar_Syntax_Syntax.eff_name = uu___116_8182.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___116_8182.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___116_8182.FStar_Syntax_Syntax.comp})
in (

let uu____8183 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (uu____8183) with
| (lbs, e2) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2))))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (uu____8212) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let uu___117_8217 = cres
in {FStar_Syntax_Syntax.eff_name = uu___117_8217.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___117_8217.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___117_8217.FStar_Syntax_Syntax.comp})
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
| uu____8220 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let uu____8236 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____8236) with
| (uu____8242, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let uu____8253 = (FStar_List.fold_left (fun uu____8260 lb -> (match (uu____8260) with
| (lbs, env) -> begin
(

let uu____8272 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (uu____8272) with
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
| uu____8285 -> begin
(

let uu____8286 = (let _0_580 = (let _0_579 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _0_579))
in (tc_check_tot_or_gtot_term (

let uu___118_8290 = env0
in {FStar_TypeChecker_Env.solver = uu___118_8290.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___118_8290.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___118_8290.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___118_8290.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___118_8290.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___118_8290.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___118_8290.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___118_8290.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___118_8290.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___118_8290.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___118_8290.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___118_8290.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___118_8290.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___118_8290.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___118_8290.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___118_8290.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___118_8290.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___118_8290.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___118_8290.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___118_8290.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___118_8290.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___118_8290.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___118_8290.FStar_TypeChecker_Env.qname_and_index}) t _0_580))
in (match (uu____8286) with
| (t, uu____8294, g) -> begin
(

let g = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((let _0_581 = (FStar_TypeChecker_Rel.discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _0_581));
(norm env0 t);
))
end))
end)
in (

let env = (

let uu____8299 = ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env))
in (match (uu____8299) with
| true -> begin
(

let uu___119_8300 = env
in {FStar_TypeChecker_Env.solver = uu___119_8300.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_8300.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_8300.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_8300.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_8300.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_8300.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_8300.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_8300.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_8300.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_8300.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_8300.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_8300.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_8300.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_8300.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_8300.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_8300.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_8300.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___119_8300.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___119_8300.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___119_8300.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_8300.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_8300.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_8300.FStar_TypeChecker_Env.qname_and_index})
end
| uu____8307 -> begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end))
in (

let lb = (

let uu___120_8310 = lb
in {FStar_Syntax_Syntax.lbname = uu___120_8310.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___120_8310.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____8253) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____8324 = (let _0_583 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____8343 = (let _0_582 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _0_582 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____8343) with
| (e, c, g) -> begin
((

let uu____8353 = (not ((FStar_Syntax_Util.is_total_lcomp c)))
in (match (uu____8353) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____8354 -> begin
()
end));
(

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g)));
)
end)))))
in (FStar_All.pipe_right _0_583 FStar_List.unzip))
in (match (uu____8324) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____8375 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____8375) with
| (env1, uu____8385) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____8391 = (check_lbtyp top_level env lb)
in (match (uu____8391) with
| (topt, wf_annot, univ_vars, univ_opening, env1) -> begin
((match (((not (top_level)) && (univ_vars <> []))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____8414 -> begin
()
end);
(

let e1 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____8417 = (tc_maybe_toplevel_term (

let uu___121_8421 = env1
in {FStar_TypeChecker_Env.solver = uu___121_8421.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___121_8421.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___121_8421.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___121_8421.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___121_8421.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___121_8421.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___121_8421.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___121_8421.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___121_8421.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___121_8421.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___121_8421.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___121_8421.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___121_8421.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___121_8421.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___121_8421.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___121_8421.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___121_8421.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___121_8421.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___121_8421.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___121_8421.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___121_8421.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___121_8421.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___121_8421.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (uu____8417) with
| (e1, c1, g1) -> begin
(

let uu____8430 = (let _0_584 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun uu____8435 -> FStar_TypeChecker_Err.ill_kinded_type))) _0_584 e1 c1 wf_annot))
in (match (uu____8430) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____8445 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____8445) with
| true -> begin
(let _0_587 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _0_586 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (let _0_585 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" _0_587 _0_586 _0_585))))
end
| uu____8446 -> begin
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
| uu____8467 -> begin
()
end);
((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____8471 -> begin
(

let uu____8472 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____8472) with
| (univ_opening, univ_vars) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(let _0_588 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (univ_opening), (_0_588)))
end
| uu____8502 -> begin
(

let uu____8503 = (FStar_Syntax_Util.type_u ())
in (match (uu____8503) with
| (k, uu____8514) -> begin
(

let uu____8515 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____8515) with
| (t, uu____8527, g) -> begin
((

let uu____8530 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8530) with
| true -> begin
(let _0_590 = (FStar_Range.string_of_range (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname))
in (let _0_589 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _0_590 _0_589)))
end
| uu____8531 -> begin
()
end));
(

let t = (norm env1 t)
in (let _0_591 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (univ_opening), (_0_591))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____8537 -> (match (uu____8537) with
| (x, imp) -> begin
(

let uu____8548 = (FStar_Syntax_Util.type_u ())
in (match (uu____8548) with
| (tu, u) -> begin
((

let uu____8560 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____8560) with
| true -> begin
(let _0_594 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_593 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _0_592 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _0_594 _0_593 _0_592))))
end
| uu____8561 -> begin
()
end));
(

let uu____8562 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____8562) with
| (t, uu____8573, g) -> begin
(

let x = (((

let uu___122_8578 = x
in {FStar_Syntax_Syntax.ppname = uu___122_8578.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___122_8578.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____8580 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8580) with
| true -> begin
(let _0_596 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _0_595 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _0_596 _0_595)))
end
| uu____8581 -> begin
()
end));
(let _0_597 = (push_binding env x)
in ((x), (_0_597), (g), (u)));
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

let uu____8632 = (tc_binder env b)
in (match (uu____8632) with
| (b, env', g, u) -> begin
(

let uu____8655 = (aux env' bs)
in (match (uu____8655) with
| (bs, env', g', us) -> begin
(let _0_599 = (let _0_598 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _0_598))
in (((b)::bs), (env'), (_0_599), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun uu____8729 uu____8730 -> (match (((uu____8729), (uu____8730))) with
| ((t, imp), (args, g)) -> begin
(

let uu____8767 = (tc_term env t)
in (match (uu____8767) with
| (t, uu____8777, g') -> begin
(let _0_600 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_0_600)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____8799 -> (match (uu____8799) with
| (pats, g) -> begin
(

let uu____8825 = (tc_args env p)
in (match (uu____8825) with
| (args, g') -> begin
(let _0_601 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_0_601)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____8864 = (tc_maybe_toplevel_term env e)
in (match (uu____8864) with
| (e, c, g) -> begin
(

let uu____8874 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____8874) with
| true -> begin
((e), (c), (g))
end
| uu____8878 -> begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let c = (norm_c env c)
in (

let uu____8884 = (

let uu____8887 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c))
in (match (uu____8887) with
| true -> begin
(let _0_602 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_0_602), (false)))
end
| uu____8890 -> begin
(let _0_603 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_0_603), (true)))
end))
in (match (uu____8884) with
| (target_comp, allow_ghost) -> begin
(

let uu____8896 = (FStar_TypeChecker_Rel.sub_comp env c target_comp)
in (match (uu____8896) with
| Some (g') -> begin
(let _0_604 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_0_604)))
end
| uu____8902 -> begin
(match (allow_ghost) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_605 = (FStar_TypeChecker_Err.expected_ghost_expression e c)
in ((_0_605), (e.FStar_Syntax_Syntax.pos))))))
end
| uu____8910 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_606 = (FStar_TypeChecker_Err.expected_pure_expression e c)
in ((_0_606), (e.FStar_Syntax_Syntax.pos))))))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____8923 = (tc_tot_or_gtot_term env t)
in (match (uu____8923) with
| (t, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____8943 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____8943) with
| true -> begin
(let _0_607 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _0_607))
end
| uu____8944 -> begin
()
end));
(

let env = (

let uu___123_8946 = env
in {FStar_TypeChecker_Env.solver = uu___123_8946.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___123_8946.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___123_8946.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___123_8946.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___123_8946.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___123_8946.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___123_8946.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___123_8946.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___123_8946.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___123_8946.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___123_8946.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___123_8946.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___123_8946.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___123_8946.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___123_8946.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___123_8946.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___123_8946.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___123_8946.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___123_8946.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___123_8946.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___123_8946.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___123_8946.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___123_8946.FStar_TypeChecker_Env.qname_and_index})
in (

let uu____8947 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Errors.Error (msg, uu____8963) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_608 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_0_608))))))
end
in (match (uu____8947) with
| (t, c, g) -> begin
(

let uu____8973 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____8973) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____8979 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_611 = (let _0_609 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _0_609))
in (let _0_610 = (FStar_TypeChecker_Env.get_range env)
in ((_0_611), (_0_610)))))))
end))
end)));
))


let level_of_type_fail = (fun env e t -> (Prims.raise (FStar_Errors.Error ((let _0_614 = (let _0_612 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _0_612 t))
in (let _0_613 = (FStar_TypeChecker_Env.get_range env)
in ((_0_614), (_0_613))))))))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t -> (

let uu____9016 = (FStar_Syntax_Util.unrefine t).FStar_Syntax_Syntax.n
in (match (uu____9016) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____9018 -> begin
(match (retry) with
| true -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (aux false t))
end
| uu____9020 -> begin
(

let uu____9021 = (FStar_Syntax_Util.type_u ())
in (match (uu____9021) with
| (t_u, u) -> begin
(

let env = (

let uu___126_9027 = env
in {FStar_TypeChecker_Env.solver = uu___126_9027.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___126_9027.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___126_9027.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___126_9027.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___126_9027.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___126_9027.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___126_9027.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___126_9027.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___126_9027.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___126_9027.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___126_9027.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___126_9027.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___126_9027.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___126_9027.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___126_9027.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___126_9027.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___126_9027.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___126_9027.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___126_9027.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___126_9027.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___126_9027.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___126_9027.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___126_9027.FStar_TypeChecker_Env.qname_and_index})
in (

let g = (FStar_TypeChecker_Rel.teq env t t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _0_615 = (FStar_Syntax_Print.term_to_string t)
in (level_of_type_fail env e _0_615))
end
| uu____9031 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____9040 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____9040) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____9047) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____9058) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____9083, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____9098) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n) -> begin
n.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____9105 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9105) with
| (uu____9114, t) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____9116, FStar_Util.Inl (t), uu____9118) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____9137, FStar_Util.Inr (c), uu____9139) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u)))) None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____9169; FStar_Syntax_Syntax.pos = uu____9170; FStar_Syntax_Syntax.vars = uu____9171}, us) -> begin
(

let uu____9177 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____9177) with
| (us', t) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_616 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_0_616))))))
end
| uu____9193 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____9200 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____9201) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____9209) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____9226 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____9226) with
| (bs, c) -> begin
(

let us = (FStar_List.map (fun uu____9237 -> (match (uu____9237) with
| (b, uu____9241) -> begin
(let _0_617 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort _0_617))
end)) bs)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c)
in (let _0_618 = (universe_of_aux env res)
in (level_of_type env res _0_618)))
in (

let u_c = (

let uu____9247 = (FStar_TypeChecker_Util.effect_repr env c u_res)
in (match (uu____9247) with
| None -> begin
u_res
end
| Some (trepr) -> begin
(let _0_619 = (universe_of_aux env trepr)
in (level_of_type env trepr _0_619))
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
(let _0_620 = (universe_of_aux env hd)
in ((_0_620), (args)))
end
| FStar_Syntax_Syntax.Tm_match (uu____9342, (hd)::uu____9344) -> begin
(

let uu____9391 = (FStar_Syntax_Subst.open_branch hd)
in (match (uu____9391) with
| (uu____9401, uu____9402, hd) -> begin
(

let uu____9418 = (FStar_Syntax_Util.head_and_args hd)
in (match (uu____9418) with
| (hd, args) -> begin
(type_of_head retry hd args)
end))
end))
end
| uu____9453 when retry -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____9455 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____9455) with
| (hd, args) -> begin
(type_of_head false hd args)
end)))
end
| uu____9490 -> begin
(

let uu____9491 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9491) with
| (env, uu____9505) -> begin
(

let env = (

let uu___127_9509 = env
in {FStar_TypeChecker_Env.solver = uu___127_9509.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___127_9509.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___127_9509.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___127_9509.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___127_9509.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___127_9509.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___127_9509.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___127_9509.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___127_9509.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___127_9509.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___127_9509.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___127_9509.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___127_9509.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___127_9509.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___127_9509.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___127_9509.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___127_9509.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___127_9509.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___127_9509.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___127_9509.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___127_9509.FStar_TypeChecker_Env.qname_and_index})
in ((

let uu____9511 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("UniverseOf")))
in (match (uu____9511) with
| true -> begin
(let _0_622 = (FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range env))
in (let _0_621 = (FStar_Syntax_Print.term_to_string hd)
in (FStar_Util.print2 "%s: About to type-check %s\n" _0_622 _0_621)))
end
| uu____9512 -> begin
()
end));
(

let uu____9513 = (tc_term env hd)
in (match (uu____9513) with
| (uu____9526, {FStar_Syntax_Syntax.eff_name = uu____9527; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____9529; FStar_Syntax_Syntax.comp = uu____9530}, g) -> begin
((let _0_623 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right _0_623 Prims.ignore));
((t), (args));
)
end));
))
end))
end)))
in (

let uu____9547 = (type_of_head true hd args)
in (match (uu____9547) with
| (t, args) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____9576 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____9576) with
| (bs, res) -> begin
(

let res = (FStar_Syntax_Util.comp_result res)
in (match (((FStar_List.length bs) = (FStar_List.length args))) with
| true -> begin
(

let subst = (FStar_Syntax_Util.subst_of_list bs args)
in (FStar_Syntax_Subst.subst subst res))
end
| uu____9608 -> begin
(let _0_624 = (FStar_Syntax_Print.term_to_string res)
in (level_of_type_fail env e _0_624))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____9611, (hd)::uu____9613) -> begin
(

let uu____9660 = (FStar_Syntax_Subst.open_branch hd)
in (match (uu____9660) with
| (uu____9663, uu____9664, hd) -> begin
(universe_of_aux env hd)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____9680, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (let _0_625 = (universe_of_aux env e)
in (level_of_type env e _0_625)))




