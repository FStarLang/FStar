
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _0_236 = (FStar_TypeChecker_Env.get_range env)
in (let _0_235 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.report _0_236 _0_235))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____15 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____15) with
| FStar_Syntax_Syntax.Tm_type (uu____16) -> begin
true
end
| uu____17 -> begin
false
end)))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env -> (let _0_237 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _0_237 (FStar_List.filter (fun uu____29 -> (match (uu____29) with
| (x, uu____33) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = (

let uu____43 = ((FStar_Options.full_context_dependency ()) || (let _0_238 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_238)))
in (match (uu____43) with
| true -> begin
(FStar_TypeChecker_Env.all_binders env)
end
| uu____44 -> begin
(t_binders env)
end))
in (let _0_239 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _0_239 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (Prims.fst (new_uvar_aux env k)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___90_53 -> (match (uu___90_53) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, uu____55); FStar_Syntax_Syntax.tk = uu____56; FStar_Syntax_Syntax.pos = uu____57; FStar_Syntax_Syntax.vars = uu____58} -> begin
uv
end
| uu____73 -> begin
(failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (

let uu____92 = (FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)
in (match (uu____92) with
| Some ((uu____105)::((tm, uu____107))::[]) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))) None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| uu____151 -> begin
(

let uu____158 = (new_uvar_aux env k)
in (match (uu____158) with
| (t, u) -> begin
(

let g = (

let uu___110_170 = FStar_TypeChecker_Rel.trivial_guard
in (let _0_242 = (let _0_241 = (let _0_240 = (as_uvar u)
in ((reason), (env), (_0_240), (t), (k), (r)))
in (_0_241)::[])
in {FStar_TypeChecker_Env.guard_f = uu___110_170.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___110_170.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___110_170.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _0_242}))
in (let _0_245 = (let _0_244 = (let _0_243 = (as_uvar u)
in ((_0_243), (r)))
in (_0_244)::[])
in ((t), (_0_245), (g))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____200 = (not ((FStar_Util.set_is_empty uvs)))
in (match (uu____200) with
| true -> begin
(

let us = (let _0_247 = (let _0_246 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun uu____211 -> (match (uu____211) with
| (x, uu____219) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _0_246))
in (FStar_All.pipe_right _0_247 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(let _0_249 = (let _0_248 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _0_248))
in (FStar_Errors.report r _0_249));
(FStar_Options.pop ());
))
end
| uu____237 -> begin
()
end))))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (

let uu____245 = (FStar_ST.read s.FStar_Syntax_Syntax.tk)
in (match (uu____245) with
| None -> begin
(failwith (let _0_251 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _0_250 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _0_251 _0_250))))
end
| Some (tk) -> begin
tk
end)))


let force_sort = (fun s -> ((FStar_Syntax_Syntax.mk (force_sort' s)) None s.FStar_Syntax_Syntax.pos))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____280 -> (match (uu____280) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____287; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((match ((univ_vars <> [])) with
| true -> begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end
| uu____308 -> begin
()
end);
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (

let uu____319 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
in (match (uu____319) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____322 = (FStar_Syntax_Util.type_u ())
in (match (uu____322) with
| (k, uu____328) -> begin
(

let t = (let _0_252 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _0_252 Prims.fst))
in (((

let uu___111_332 = a
in {FStar_Syntax_Syntax.ppname = uu___111_332.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___111_332.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
end))
end
| uu____333 -> begin
((a), (true))
end)))
in (

let rec aux = (fun must_check_ty vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, uu____358) -> begin
(aux must_check_ty vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, uu____365) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____392) -> begin
(

let uu____415 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____439 uu____440 -> (match (((uu____439), (uu____440))) with
| ((scope, bs, must_check_ty), (a, imp)) -> begin
(

let uu____482 = (match (must_check_ty) with
| true -> begin
((a), (true))
end
| uu____487 -> begin
(mk_binder scope a)
end)
in (match (uu____482) with
| (tb, must_check_ty) -> begin
(

let b = ((tb), (imp))
in (

let bs = (FStar_List.append bs ((b)::[]))
in (

let scope = (FStar_List.append scope ((b)::[]))
in ((scope), (bs), (must_check_ty)))))
end))
end)) ((vars), ([]), (must_check_ty))))
in (match (uu____415) with
| (scope, bs, must_check_ty) -> begin
(

let uu____543 = (aux must_check_ty scope body)
in (match (uu____543) with
| (res, must_check_ty) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t) -> begin
(

let uu____560 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)
in (match (uu____560) with
| None -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____562 -> begin
(FStar_Syntax_Util.ml_comp t r)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t = (FStar_Syntax_Util.arrow bs c)
in ((

let uu____569 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____569) with
| true -> begin
(let _0_255 = (FStar_Range.string_of_range r)
in (let _0_254 = (FStar_Syntax_Print.term_to_string t)
in (let _0_253 = (FStar_Util.string_of_bool must_check_ty)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" _0_255 _0_254 _0_253))))
end
| uu____570 -> begin
()
end));
((FStar_Util.Inl (t)), (must_check_ty));
)))
end))
end))
end
| uu____577 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end
| uu____584 -> begin
(let _0_257 = FStar_Util.Inl ((let _0_256 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _0_256 Prims.fst)))
in ((_0_257), (false)))
end)
end)))
in (

let uu____589 = (let _0_258 = (t_binders env)
in (aux false _0_258 e))
in (match (uu____589) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(

let uu____610 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____610) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____613 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_260 = (let _0_259 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _0_259))
in ((_0_260), (rng))))))
end))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end)))));
)
end
| uu____620 -> begin
(

let uu____621 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (uu____621) with
| (univ_vars, t) -> begin
((univ_vars), (t), (false))
end))
end)))
end))


let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c))) None p.FStar_Syntax_Syntax.p)
in (([]), ([]), ([]), (env), (e), (p)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____704) -> begin
(

let uu____709 = (FStar_Syntax_Util.type_u ())
in (match (uu____709) with
| (k, uu____722) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let uu___112_725 = x
in {FStar_Syntax_Syntax.ppname = uu___112_725.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_725.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____726 = (let _0_261 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _0_261 t))
in (match (uu____726) with
| (e, u) -> begin
(

let p = (

let uu___113_743 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = uu___113_743.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___113_743.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____750 = (FStar_Syntax_Util.type_u ())
in (match (uu____750) with
| (t, uu____763) -> begin
(

let x = (

let uu___114_765 = x
in (let _0_262 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = uu___114_765.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_765.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_262}))
in (

let env = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env x)
end
| uu____767 -> begin
env
end)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x))) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ([]), ((x)::[]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____785 = (FStar_Syntax_Util.type_u ())
in (match (uu____785) with
| (t, uu____798) -> begin
(

let x = (

let uu___115_800 = x
in (let _0_263 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = uu___115_800.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_800.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_263}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x))) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____830 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____886 uu____887 -> (match (((uu____886), (uu____887))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let uu____986 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (uu____986) with
| (b', a', w', env, te, pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1025 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (((b')::b), ((a')::a), ((w')::w), (env), ((arg)::args), ((((pat), (imp)))::pats)))
end))
end)) (([]), ([]), ([]), (env), ([]), ([]))))
in (match (uu____830) with
| (b, a, w, env, args, pats) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((let _0_266 = ((let _0_265 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _0_264 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _0_265 _0_264))) None p.FStar_Syntax_Syntax.p)
in ((_0_266), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))) None p.FStar_Syntax_Syntax.p)
in (let _0_269 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _0_268 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _0_267 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_0_269), (_0_268), (_0_267), (env), (e), ((

let uu___116_1131 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___116_1131.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___116_1131.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (uu____1137) -> begin
(failwith "impossible")
end))
in (

let rec elaborate_pat = (fun env p -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end
| uu____1177 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats = (FStar_List.map (fun uu____1206 -> (match (uu____1206) with
| (p, imp) -> begin
(let _0_270 = (elaborate_pat env p)
in ((_0_270), (imp)))
end)) pats)
in (

let uu____1223 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1223) with
| (uu____1232, t) -> begin
(

let uu____1234 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1234) with
| (f, uu____1245) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (uu____1320)::uu____1321) -> begin
(Prims.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((uu____1356)::uu____1357, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____1397 -> (match (uu____1397) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _0_271 = Some ((FStar_Syntax_Syntax.range_of_bv t))
in (FStar_Syntax_Syntax.new_bv _0_271 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _0_272 = (maybe_dot inaccessible a r)
in ((_0_272), (true)))))
end
| uu____1422 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_274 = (let _0_273 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _0_273))
in ((_0_274), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (uu____1474, Some (FStar_Syntax_Syntax.Implicit (uu____1475))) when p_imp -> begin
(let _0_275 = (aux formals' pats')
in (((p), (true)))::_0_275)
end
| (uu____1483, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _0_276 = (aux formals' pats)
in (((p), (true)))::_0_276)))
end
| (uu____1500, imp) -> begin
(let _0_279 = (let _0_277 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_0_277)))
in (let _0_278 = (aux formals' pats')
in (_0_279)::_0_278))
end)
end))
in (

let uu___117_1510 = p
in (let _0_281 = FStar_Syntax_Syntax.Pat_cons ((let _0_280 = (aux f pats)
in ((fv), (_0_280))))
in {FStar_Syntax_Syntax.v = _0_281; FStar_Syntax_Syntax.ty = uu___117_1510.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___117_1510.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____1518 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let uu____1544 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (uu____1544) with
| (b, a, w, env, arg, p) -> begin
(

let uu____1574 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____1574) with
| Some (x) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_282 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in ((_0_282), (p.FStar_Syntax_Syntax.p))))))
end
| uu____1595 -> begin
((b), (a), (w), (arg), (p))
end))
end))))
in (

let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((q)::pats) -> begin
(

let uu____1638 = (one_pat false env q)
in (match (uu____1638) with
| (b, a, uu____1654, te, q) -> begin
(

let uu____1663 = (FStar_List.fold_right (fun p uu____1679 -> (match (uu____1679) with
| (w, args, pats) -> begin
(

let uu____1703 = (one_pat false env p)
in (match (uu____1703) with
| (b', a', w', arg, p) -> begin
(

let uu____1729 = (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a')))
in (match (uu____1729) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_284 = (FStar_TypeChecker_Err.disjunctive_pattern_vars a a')
in (let _0_283 = (FStar_TypeChecker_Env.get_range env)
in ((_0_284), (_0_283)))))))
end
| uu____1742 -> begin
(let _0_286 = (let _0_285 = (FStar_Syntax_Syntax.as_arg arg)
in (_0_285)::args)
in (((FStar_List.append w' w)), (_0_286), ((p)::pats)))
end))
end))
end)) pats (([]), ([]), ([])))
in (match (uu____1663) with
| (w, args, pats) -> begin
(let _0_288 = (let _0_287 = (FStar_Syntax_Syntax.as_arg te)
in (_0_287)::args)
in (((FStar_List.append b w)), (_0_288), ((

let uu___118_1767 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = uu___118_1767.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___118_1767.FStar_Syntax_Syntax.p}))))
end))
end))
end
| uu____1768 -> begin
(

let uu____1769 = (one_pat true env p)
in (match (uu____1769) with
| (b, uu____1784, uu____1785, arg, p) -> begin
(let _0_290 = (let _0_289 = (FStar_Syntax_Syntax.as_arg arg)
in (_0_289)::[])
in ((b), (_0_290), (p)))
end))
end))
in (

let uu____1796 = (top_level_pat_as_args env p)
in (match (uu____1796) with
| (b, args, p) -> begin
(

let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in ((b), (exps), (p)))
end)))))))


let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (

let qq = p
in (

let rec aux = (fun p e -> (

let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (

let e = (FStar_Syntax_Util.unmeta e)
in (match (((p.FStar_Syntax_Syntax.v), (e.FStar_Syntax_Syntax.n))) with
| (uu____1867, FStar_Syntax_Syntax.Tm_uinst (e, uu____1869)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____1874), FStar_Syntax_Syntax.Tm_constant (uu____1875)) -> begin
(let _0_291 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _0_291))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(failwith (let _0_293 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_292 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _0_293 _0_292))))
end
| uu____1879 -> begin
()
end);
(

let uu____1881 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____1881) with
| true -> begin
(let _0_295 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_294 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _0_295 _0_294)))
end
| uu____1882 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___119_1885 = x
in {FStar_Syntax_Syntax.ppname = uu___119_1885.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_1885.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____1889 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____1889) with
| true -> begin
(failwith (let _0_297 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_296 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _0_297 _0_296))))
end
| uu____1890 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___120_1893 = x
in {FStar_Syntax_Syntax.ppname = uu___120_1893.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_1893.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____1895), uu____1896) -> begin
(

let s = (force_sort e)
in (

let x = (

let uu___121_1905 = x
in {FStar_Syntax_Syntax.ppname = uu___121_1905.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_1905.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____1918 = (not ((FStar_Syntax_Syntax.fv_eq fv fv')))
in (match (uu____1918) with
| true -> begin
(failwith (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str))
end
| uu____1927 -> begin
()
end));
(let _0_298 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _0_298));
)
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
((

let uu____1998 = (let _0_299 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _0_299 Prims.op_Negation))
in (match (uu____1998) with
| true -> begin
(failwith (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str))
end
| uu____2007 -> begin
()
end));
(

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _0_300 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _0_300))
end
| ((arg)::args, ((argpat, uu____2098))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____2148)) -> begin
(

let x = (let _0_301 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _0_301))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), uu____2177) -> begin
(

let pat = (let _0_303 = (aux argpat e)
in (let _0_302 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_0_303), (_0_302))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| uu____2194 -> begin
(failwith (let _0_305 = (FStar_Syntax_Print.pat_to_string p)
in (let _0_304 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _0_305 _0_304))))
end))
in (match_args [] args argpats)));
)
end
| uu____2214 -> begin
(failwith (let _0_309 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _0_308 = (FStar_Syntax_Print.pat_to_string qq)
in (let _0_307 = (let _0_306 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _0_306 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _0_309 _0_308 _0_307)))))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), uu____2222) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (uu____2238, (e)::[]) -> begin
(aux p e)
end
| uu____2241 -> begin
(failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> ((FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____2280 -> (match (uu____2280) with
| (p, i) -> begin
(

let uu____2290 = (decorated_pattern_as_term p)
in (match (uu____2290) with
| (vars, te) -> begin
(let _0_311 = (let _0_310 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_0_310)))
in ((vars), (_0_311)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____2309) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _0_312 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_0_312)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _0_313 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_0_313)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2336 = (let _0_314 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _0_314 FStar_List.unzip))
in (match (uu____2336) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _0_316 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_315 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_0_315), (args))))))
in ((vars), (_0_316))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____2425))::[] -> begin
wp
end
| uu____2438 -> begin
(failwith (let _0_318 = (let _0_317 = (FStar_List.map (fun uu____2449 -> (match (uu____2449) with
| (x, uu____2453) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _0_317 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _0_318)))
end)
in (let _0_319 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_0_319), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____2481 = (destruct_comp c)
in (match (uu____2481) with
| (u, uu____2486, wp) -> begin
(let _0_321 = (let _0_320 = (FStar_Syntax_Syntax.as_arg (lift c.FStar_Syntax_Syntax.result_typ wp))
in (_0_320)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _0_321; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____2497 = (let _0_323 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _0_322 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _0_323 _0_322)))
in (match (uu____2497) with
| (m, uu____2502, uu____2503) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____2513 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____2513) with
| true -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| uu____2514 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (

let uu____2538 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (uu____2538) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____2568 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____2568) with
| (a, kwp) -> begin
(let _0_325 = (destruct_comp m1)
in (let _0_324 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_0_325), (_0_324))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (FStar_Syntax_Syntax.mk_Comp (let _0_327 = (let _0_326 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_326)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _0_327; FStar_Syntax_Syntax.flags = flags})))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (match ((FStar_Ident.lid_equals mname FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (Some (u_result)))
end
| uu____2657 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let uu___122_2664 = lc
in (let _0_329 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___122_2664.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _0_329; FStar_Syntax_Syntax.cflags = uu___122_2664.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2665 -> (let _0_328 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _0_328)))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2669 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2669) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2670) -> begin
true
end
| uu____2678 -> begin
false
end)))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = (

let uu____2689 = (let _0_330 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _0_330))
in (match (uu____2689) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____2690 -> begin
(

let m = (FStar_Util.must (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid))
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (

let uu____2694 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2694) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____2695 -> begin
(

let uu____2696 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (uu____2696) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (let _0_336 = ((let _0_335 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _0_334 = (let _0_333 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_332 = (let _0_331 = (FStar_Syntax_Syntax.as_arg v)
in (_0_331)::[])
in (_0_333)::_0_332))
in (FStar_Syntax_Syntax.mk_Tm_app _0_335 _0_334))) (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _0_336)))
end))
end))
in ((mk_comp m) u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
in ((

let uu____2709 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____2709) with
| true -> begin
(let _0_339 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _0_338 = (FStar_Syntax_Print.term_to_string v)
in (let _0_337 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _0_339 _0_338 _0_337))))
end
| uu____2710 -> begin
()
end));
c;
)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____2726 -> (match (uu____2726) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc1 lc2)
in ((

let uu____2736 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2736) with
| true -> begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _0_342 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _0_341 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _0_340 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _0_342 _0_341 bstr _0_340)))))
end
| uu____2740 -> begin
()
end));
(

let bind_it = (fun uu____2744 -> (

let uu____2745 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2745) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc2.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc2.FStar_Syntax_Syntax.res_typ []))
end
| uu____2747 -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in ((

let uu____2755 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2755) with
| true -> begin
(let _0_347 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _0_346 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _0_345 = (FStar_Syntax_Print.comp_to_string c1)
in (let _0_344 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _0_343 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _0_347 _0_346 _0_345 _0_344 _0_343))))))
end
| uu____2757 -> begin
()
end));
(

let try_simplify = (fun uu____2764 -> (

let aux = (fun uu____2773 -> (

let uu____2774 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____2774) with
| true -> begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (uu____2791) -> begin
(

let uu____2792 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____2792) with
| true -> begin
Some (((c2), ("trivial ml")))
end
| uu____2804 -> begin
None
end))
end)
end
| uu____2809 -> begin
(

let uu____2810 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____2810) with
| true -> begin
Some (((c2), ("both ml")))
end
| uu____2822 -> begin
None
end))
end)))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
Some ((let _0_348 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_0_348), (reason))))
end
| uu____2845 -> begin
(aux ())
end))
in (

let uu____2850 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____2850) with
| true -> begin
(subst_c2 "both total")
end
| uu____2854 -> begin
(

let uu____2855 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____2855) with
| true -> begin
Some ((let _0_349 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_0_349), ("both gtot"))))
end
| uu____2861 -> begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
(

let uu____2871 = ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x))))
in (match (uu____2871) with
| true -> begin
(subst_c2 "substituted e")
end
| uu____2875 -> begin
(aux ())
end))
end
| uu____2876 -> begin
(aux ())
end)
end))
end)))))
in (

let uu____2881 = (try_simplify ())
in (match (uu____2881) with
| Some (c, reason) -> begin
c
end
| None -> begin
(

let uu____2891 = (lift_and_destruct env c1 c2)
in (match (uu____2891) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _0_350 = (FStar_Syntax_Syntax.null_binder t1)
in (_0_350)::[])
end
| Some (x) -> begin
(let _0_351 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_351)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)))) None r1)
in (

let wp_args = (let _0_360 = (FStar_Syntax_Syntax.as_arg r1)
in (let _0_359 = (let _0_358 = (FStar_Syntax_Syntax.as_arg t1)
in (let _0_357 = (let _0_356 = (FStar_Syntax_Syntax.as_arg t2)
in (let _0_355 = (let _0_354 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _0_353 = (let _0_352 = (FStar_Syntax_Syntax.as_arg (mk_lam wp2))
in (_0_352)::[])
in (_0_354)::_0_353))
in (_0_356)::_0_355))
in (_0_358)::_0_357))
in (_0_360)::_0_359))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = ((let _0_361 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _0_361 wp_args)) None t2.FStar_Syntax_Syntax.pos)
in (

let c = ((mk_comp md) u_t2 t2 wp [])
in c)))))))
end))
end)));
)))
end)))
in {FStar_Syntax_Syntax.eff_name = joined_eff; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it});
))))
end))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false)))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
(

let uu____3004 = (let _0_362 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _0_362))
in (match (uu____3004) with
| true -> begin
f
end
| uu____3005 -> begin
(let _0_363 = (reason ())
in (label _0_363 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___123_3016 = g
in (let _0_364 = FStar_TypeChecker_Common.NonTrivial ((label reason r f))
in {FStar_TypeChecker_Env.guard_f = _0_364; FStar_TypeChecker_Env.deferred = uu___123_3016.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___123_3016.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___123_3016.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____3026 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____3043 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3047 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3047) with
| true -> begin
c
end
| uu____3050 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____3054 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3054) with
| true -> begin
c
end
| uu____3057 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3059 = (destruct_comp c)
in (match (uu____3059) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = ((let _0_371 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _0_370 = (let _0_369 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_368 = (let _0_367 = (FStar_Syntax_Syntax.as_arg f)
in (let _0_366 = (let _0_365 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_365)::[])
in (_0_367)::_0_366))
in (_0_369)::_0_368))
in (FStar_Syntax_Syntax.mk_Tm_app _0_371 _0_370))) None wp.FStar_Syntax_Syntax.pos)
in ((mk_comp md) u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end))
end)
end))))
in (

let uu___124_3076 = lc
in {FStar_Syntax_Syntax.eff_name = uu___124_3076.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___124_3076.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___124_3076.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> (

let uu____3103 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____3103) with
| true -> begin
((lc), (g0))
end
| uu____3106 -> begin
((

let uu____3108 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3108) with
| true -> begin
(let _0_373 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _0_372 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _0_373 _0_372)))
end
| uu____3109 -> begin
()
end));
(

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___91_3114 -> (match (uu___91_3114) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| uu____3116 -> begin
[]
end))))
in (

let strengthen = (fun uu____3122 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____3128 -> begin
(

let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____3130 = (FStar_TypeChecker_Rel.guard_form g0)
in (match (uu____3130) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c = (

let uu____3137 = ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c))))
in (match (uu____3137) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (

let xret = (let _0_375 = (let _0_374 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _0_374))
in (FStar_Syntax_Util.comp_set_flags _0_375 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end
| uu____3146 -> begin
c
end))
in ((

let uu____3148 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3148) with
| true -> begin
(let _0_377 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _0_376 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _0_377 _0_376)))
end
| uu____3149 -> begin
()
end));
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3151 = (destruct_comp c)
in (match (uu____3151) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = ((let _0_386 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _0_385 = (let _0_384 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_383 = (let _0_382 = (let _0_379 = (let _0_378 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _0_378 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_379))
in (let _0_381 = (let _0_380 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_380)::[])
in (_0_382)::_0_381))
in (_0_384)::_0_383))
in (FStar_Syntax_Syntax.mk_Tm_app _0_386 _0_385))) None wp.FStar_Syntax_Syntax.pos)
in ((

let uu____3169 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3169) with
| true -> begin
(let _0_387 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _0_387))
end
| uu____3170 -> begin
()
end));
(

let c2 = ((mk_comp md) u_res_t res_t wp flags)
in c2);
)))
end)));
))
end)))
end)))
in (let _0_391 = (

let uu___125_3172 = lc
in (let _0_390 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _0_389 = (

let uu____3173 = ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _0_388 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _0_388)))
in (match (uu____3173) with
| true -> begin
flags
end
| uu____3175 -> begin
[]
end))
in {FStar_Syntax_Syntax.eff_name = _0_390; FStar_Syntax_Syntax.res_typ = uu___125_3172.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _0_389; FStar_Syntax_Syntax.comp = strengthen})))
in ((_0_391), ((

let uu___126_3176 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___126_3176.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___126_3176.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___126_3176.FStar_TypeChecker_Env.implicits}))))));
)
end)))


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let uu____3191 = (let _0_393 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _0_392 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_0_393), (_0_392))))
in (match (uu____3191) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = ((let _0_398 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _0_397 = (let _0_396 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_395 = (let _0_394 = (FStar_Syntax_Syntax.as_arg yexp)
in (_0_394)::[])
in (_0_396)::_0_395))
in (FStar_Syntax_Syntax.mk_Tm_app _0_398 _0_397))) None res_t.FStar_Syntax_Syntax.pos)
in (

let x_eq_y_yret = ((let _0_406 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _0_405 = (let _0_404 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_403 = (let _0_402 = (let _0_399 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_399))
in (let _0_401 = (let _0_400 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_0_400)::[])
in (_0_402)::_0_401))
in (_0_404)::_0_403))
in (FStar_Syntax_Syntax.mk_Tm_app _0_406 _0_405))) None res_t.FStar_Syntax_Syntax.pos)
in (

let forall_y_x_eq_y_yret = ((let _0_416 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _0_415 = (let _0_414 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_413 = (let _0_412 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_411 = (let _0_410 = (let _0_409 = (let _0_408 = (let _0_407 = (FStar_Syntax_Syntax.mk_binder y)
in (_0_407)::[])
in (FStar_Syntax_Util.abs _0_408 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_409))
in (_0_410)::[])
in (_0_412)::_0_411))
in (_0_414)::_0_413))
in (FStar_Syntax_Syntax.mk_Tm_app _0_416 _0_415))) None res_t.FStar_Syntax_Syntax.pos)
in (

let lc2 = ((mk_comp md_pure) u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _0_417 = (FStar_TypeChecker_Env.get_range env)
in (bind _0_417 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun uu____3248 -> (

let uu____3249 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3249) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end
| uu____3251 -> begin
(

let uu____3252 = (let _0_419 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _0_418 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _0_419 _0_418)))
in (match (uu____3252) with
| ((md, uu____3266, uu____3267), (u_res_t, res_t, wp_then), (uu____3271, uu____3272, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _0_429 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in ((let _0_428 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _0_427 = (let _0_426 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_425 = (let _0_424 = (FStar_Syntax_Syntax.as_arg g)
in (let _0_423 = (let _0_422 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _0_421 = (let _0_420 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_0_420)::[])
in (_0_422)::_0_421))
in (_0_424)::_0_423))
in (_0_426)::_0_425))
in (FStar_Syntax_Syntax.mk_Tm_app _0_428 _0_427))) None _0_429)))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let uu____3308 = (let _0_430 = (FStar_Options.split_cases ())
in (_0_430 > (Prims.parse_int "0")))
in (match (uu____3308) with
| true -> begin
(

let comp = ((mk_comp md) u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end
| uu____3310 -> begin
(

let wp = ((let _0_435 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _0_434 = (let _0_433 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_432 = (let _0_431 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_431)::[])
in (_0_433)::_0_432))
in (FStar_Syntax_Syntax.mk_Tm_app _0_435 _0_434))) None wp.FStar_Syntax_Syntax.pos)
in ((mk_comp md) u_res_t res_t wp []))
end))))
end))
end)))
in (let _0_436 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _0_436; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _0_438 = (let _0_437 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _0_437))
in (FStar_Syntax_Syntax.fvar _0_438 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____3343 -> (match (uu____3343) with
| (uu____3346, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun uu____3351 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____3353 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3353) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____3354 -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _0_448 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in ((let _0_447 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _0_446 = (let _0_445 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_444 = (let _0_443 = (FStar_Syntax_Syntax.as_arg g)
in (let _0_442 = (let _0_441 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _0_440 = (let _0_439 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_0_439)::[])
in (_0_441)::_0_440))
in (_0_443)::_0_442))
in (_0_445)::_0_444))
in (FStar_Syntax_Syntax.mk_Tm_app _0_447 _0_446))) None _0_448)))
in (

let default_case = (

let post_k = (let _0_451 = (let _0_449 = (FStar_Syntax_Syntax.null_binder res_t)
in (_0_449)::[])
in (let _0_450 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _0_451 _0_450)))
in (

let kwp = (let _0_454 = (let _0_452 = (FStar_Syntax_Syntax.null_binder post_k)
in (_0_452)::[])
in (let _0_453 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _0_454 _0_453)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _0_460 = (let _0_455 = (FStar_Syntax_Syntax.mk_binder post)
in (_0_455)::[])
in (let _0_459 = (let _0_458 = (let _0_456 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check _0_456))
in (let _0_457 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _0_458 _0_457)))
in (FStar_Syntax_Util.abs _0_460 _0_459 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in ((mk_comp md) u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun uu____3399 celse -> (match (uu____3399) with
| (g, cthen) -> begin
(

let uu____3405 = (let _0_461 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _0_461 celse))
in (match (uu____3405) with
| ((md, uu____3419, uu____3420), (uu____3421, uu____3422, wp_then), (uu____3424, uu____3425, wp_else)) -> begin
(let _0_462 = (ifthenelse md res_t g wp_then wp_else)
in ((mk_comp md) u_res_t res_t _0_462 []))
end))
end)) lcases default_case)
in (

let uu____3436 = (let _0_463 = (FStar_Options.split_cases ())
in (_0_463 > (Prims.parse_int "0")))
in (match (uu____3436) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| uu____3437 -> begin
(

let comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____3440 = (destruct_comp comp)
in (match (uu____3440) with
| (uu____3444, uu____3445, wp) -> begin
(

let wp = ((let _0_468 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _0_467 = (let _0_466 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_465 = (let _0_464 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_464)::[])
in (_0_466)::_0_465))
in (FStar_Syntax_Syntax.mk_Tm_app _0_468 _0_467))) None wp.FStar_Syntax_Syntax.pos)
in ((mk_comp md) u_res_t res_t wp []))
end))))
end)))))
end))))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun uu____3470 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3474 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3474) with
| true -> begin
c
end
| uu____3477 -> begin
(

let uu____3478 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3478) with
| true -> begin
c
end
| uu____3481 -> begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _0_469 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_469)::[])
in (

let us = (let _0_471 = (let _0_470 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_0_470)::[])
in (u_res)::_0_471)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in ((let _0_478 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _0_477 = (let _0_476 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_475 = (let _0_474 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _0_473 = (let _0_472 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_472)::[])
in (_0_474)::_0_473))
in (_0_476)::_0_475))
in (FStar_Syntax_Syntax.mk_Tm_app _0_478 _0_477))) None wp0.FStar_Syntax_Syntax.pos))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3527 = (destruct_comp c)
in (match (uu____3527) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (close_wp u_res_t md res_t bvs wp)
in ((mk_comp md) u_res_t c.FStar_Syntax_Syntax.result_typ wp c.FStar_Syntax_Syntax.flags)))
end))))
end))
end))))
in (

let uu___127_3538 = lc
in {FStar_Syntax_Syntax.eff_name = uu___127_3538.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___127_3538.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___127_3538.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun uu____3553 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3557 = ((not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) || env.FStar_TypeChecker_Env.lax)
in (match (uu____3557) with
| true -> begin
c
end
| uu____3560 -> begin
(

let uu____3561 = (FStar_Syntax_Util.is_partial_return c)
in (match (uu____3561) with
| true -> begin
c
end
| uu____3564 -> begin
(

let uu____3565 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid))))
in (match (uu____3565) with
| true -> begin
(failwith (let _0_480 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _0_479 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _0_480 _0_479))))
end
| uu____3570 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let t = c.FStar_Syntax_Syntax.result_typ
in (

let c = (FStar_Syntax_Syntax.mk_Comp c)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let ret = (let _0_482 = (let _0_481 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _0_481 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_482))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _0_483 = ((bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret))).FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.comp_set_flags _0_483 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end))
end))
end))))
in (

let flags = (

let uu____3595 = (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc))))
in (match (uu____3595) with
| true -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____3597 -> begin
lc.FStar_Syntax_Syntax.cflags
end))
in (

let uu___128_3598 = lc
in {FStar_Syntax_Syntax.eff_name = uu___128_3598.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___128_3598.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____3617 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____3617) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_485 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (let _0_484 = (FStar_TypeChecker_Env.get_range env)
in ((_0_485), (_0_484)))))))
end
| Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let uu____3642 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3642) with
| FStar_Syntax_Syntax.Tm_type (uu____3645) -> begin
(

let uu____3646 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n
in (match (uu____3646) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let uu____3650 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc = (let _0_488 = (let _0_487 = (let _0_486 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_486))
in ((None), (_0_487)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _0_488))
in (

let e = ((let _0_490 = (let _0_489 = (FStar_Syntax_Syntax.as_arg e)
in (_0_489)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _0_490)) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((e), (lc))))))
end
| uu____3667 -> begin
((e), (lc))
end))
end
| uu____3668 -> begin
((e), (lc))
end)))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(let _0_491 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_0_491), (false)))
end
| uu____3695 -> begin
(let _0_492 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_0_492), (true)))
end)
in (match (gopt) with
| (None, uu____3700) -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___129_3703 = lc
in {FStar_Syntax_Syntax.eff_name = uu___129_3703.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___129_3703.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___129_3703.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard));
)
end
| (Some (g), apply_guard) -> begin
(

let uu____3707 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____3707) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let uu___130_3712 = lc
in {FStar_Syntax_Syntax.eff_name = uu___130_3712.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___130_3712.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___130_3712.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let uu___131_3715 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___131_3715.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___131_3715.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___131_3715.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____3721 -> (

let uu____3722 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3722) with
| true -> begin
(lc.FStar_Syntax_Syntax.comp ())
end
| uu____3725 -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let uu____3727 = (FStar_Syntax_Subst.compress f).FStar_Syntax_Syntax.n
in (match (uu____3727) with
| FStar_Syntax_Syntax.Tm_abs (uu____3730, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____3732; FStar_Syntax_Syntax.pos = uu____3733; FStar_Syntax_Syntax.vars = uu____3734}, uu____3735) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let uu___132_3759 = lc
in {FStar_Syntax_Syntax.eff_name = uu___132_3759.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___132_3759.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___132_3759.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| uu____3760 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in ((

let uu____3765 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3765) with
| true -> begin
(let _0_496 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _0_495 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _0_494 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _0_493 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _0_496 _0_495 _0_494 _0_493)))))
end
| uu____3766 -> begin
()
end));
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3768 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (uu____3768) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____3779 = (destruct_comp ct)
in (match (uu____3779) with
| (u_t, uu____3786, uu____3787) -> begin
(

let wp = ((let _0_501 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _0_500 = (let _0_499 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_498 = (let _0_497 = (FStar_Syntax_Syntax.as_arg xexp)
in (_0_497)::[])
in (_0_499)::_0_498))
in (FStar_Syntax_Syntax.mk_Tm_app _0_501 _0_500))) (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)
in (

let cret = (let _0_502 = ((mk_comp md) u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_502))
in (

let guard = (match (apply_guard) with
| true -> begin
((let _0_504 = (let _0_503 = (FStar_Syntax_Syntax.as_arg xexp)
in (_0_503)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _0_504)) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos)
end
| uu____3807 -> begin
f
end)
in (

let uu____3808 = (let _0_508 = (FStar_All.pipe_left (fun _0_505 -> Some (_0_505)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _0_507 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _0_506 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _0_508 _0_507 e cret _0_506))))
in (match (uu____3808) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let uu___133_3823 = x
in {FStar_Syntax_Syntax.ppname = uu___133_3823.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_3823.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _0_510 = (let _0_509 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_509))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _0_510 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in ((

let uu____3832 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3832) with
| true -> begin
(let _0_511 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _0_511))
end
| uu____3833 -> begin
()
end));
c;
))))
end)))))
end))))))
end)));
))
end)))
end)))
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___92_3838 -> (match (uu___92_3838) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____3840 -> begin
[]
end))))
in (

let lc = (

let uu___134_3842 = lc
in (let _0_512 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _0_512; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let uu___135_3844 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___135_3844.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___135_3844.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___135_3844.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end))
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _0_515 = ((let _0_514 = (let _0_513 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name x))
in (_0_513)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _0_514)) None res_t.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.refine x _0_515))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____3874 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____3874) with
| true -> begin
((None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____3881 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (_)) | (FStar_Syntax_Syntax.Total (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____3898))::((ens, uu____3900))::uu____3901 -> begin
(let _0_518 = Some ((norm req))
in (let _0_517 = (let _0_516 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _0_516))
in ((_0_518), (_0_517))))
end
| uu____3924 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_520 = (let _0_519 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" _0_519))
in ((_0_520), (comp.FStar_Syntax_Syntax.pos))))))
end)
end
| uu____3933 -> begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____3939))::uu____3940 -> begin
(

let uu____3954 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (uu____3954) with
| (us_r, uu____3961) -> begin
(

let uu____3962 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (uu____3962) with
| (us_e, uu____3969) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _0_521 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_521 us_r))
in (

let as_ens = (let _0_522 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_522 us_e))
in (

let req = ((let _0_525 = (let _0_524 = (let _0_523 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_523)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_0_524)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _0_525)) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos)
in (

let ens = ((let _0_528 = (let _0_527 = (let _0_526 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_526)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_0_527)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _0_528)) None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos)
in (let _0_530 = Some ((norm req))
in (let _0_529 = (norm (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens))
in ((_0_530), (_0_529)))))))))
end))
end))
end
| uu____4004 -> begin
(failwith "Impossible")
end))
end)
end)
end)))))


let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let torig = (FStar_Syntax_Subst.compress t)
in (match ((not (env.FStar_TypeChecker_Env.instantiate_imp))) with
| true -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____4029 -> begin
(

let number_of_implicits = (fun t -> (

let uu____4034 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____4034) with
| (formals, uu____4043) -> begin
(

let n_implicits = (

let uu____4055 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____4092 -> (match (uu____4092) with
| (uu____4096, imp) -> begin
((imp = None) || (imp = Some (FStar_Syntax_Syntax.Equality)))
end))))
in (match (uu____4055) with
| None -> begin
(FStar_List.length formals)
end
| Some (implicits, _first_explicit, _rest) -> begin
(FStar_List.length implicits)
end))
in n_implicits)
end)))
in (

let inst_n_binders = (fun t -> (

let uu____4168 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____4168) with
| None -> begin
None
end
| Some (expected_t) -> begin
(

let n_expected = (number_of_implicits expected_t)
in (

let n_available = (number_of_implicits t)
in (match ((n_available < n_expected)) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_535 = (let _0_533 = (FStar_Util.string_of_int n_expected)
in (let _0_532 = (FStar_Syntax_Print.term_to_string e)
in (let _0_531 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" _0_533 _0_532 _0_531))))
in (let _0_534 = (FStar_TypeChecker_Env.get_range env)
in ((_0_535), (_0_534)))))))
end
| uu____4189 -> begin
Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___93_4200 -> (match (uu___93_4200) with
| None -> begin
None
end
| Some (i) -> begin
Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4219 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4219) with
| (bs, c) -> begin
(

let rec aux = (fun subst inst_n bs -> (match (((inst_n), (bs))) with
| (Some (_0_536), uu____4280) when (_0_536 = (Prims.parse_int "0")) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____4302, ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let uu____4321 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (uu____4321) with
| (v, uu____4342, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let uu____4352 = (aux subst (decr_inst inst_n) rest)
in (match (uu____4352) with
| (args, bs, subst, g') -> begin
(let _0_537 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_0_537)))
end)))
end)))
end
| (uu____4414, bs) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____4438 = (let _0_538 = (inst_n_binders t)
in (aux [] _0_538 bs))
in (match (uu____4438) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], uu____4488) -> begin
((e), (torig), (guard))
end
| (uu____4504, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____4520 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____4539 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let e = ((FStar_Syntax_Syntax.mk_Tm_app e args) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((e), (t), (guard)))))
end)
end)))
end))
end
| uu____4554 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs = (fun univs -> (let _0_541 = (let _0_540 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _0_540 (FStar_List.map (fun u -> (let _0_539 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _0_539 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _0_541 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____4584 = (FStar_Util.set_is_empty x)
in (match (uu____4584) with
| true -> begin
[]
end
| uu____4586 -> begin
(

let s = (let _0_543 = (let _0_542 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _0_542))
in (FStar_All.pipe_right _0_543 FStar_Util.set_elements))
in ((

let uu____4592 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____4592) with
| true -> begin
(let _0_544 = (string_of_univs (FStar_TypeChecker_Env.univ_vars env))
in (FStar_Util.print1 "univ_vars in env: %s\n" _0_544))
end
| uu____4594 -> begin
()
end));
(

let r = Some ((FStar_TypeChecker_Env.get_range env))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____4608 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____4608) with
| true -> begin
(let _0_548 = (let _0_545 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _0_545))
in (let _0_547 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _0_546 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _0_548 _0_547 _0_546))))
end
| uu____4610 -> begin
()
end));
(FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))));
u_name;
)))))
in u_names));
))
end)))


let gather_free_univnames : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env t -> (

let ctx_univnames = (FStar_TypeChecker_Env.univnames env)
in (

let tm_univnames = (FStar_Syntax_Free.univnames t)
in (

let univnames = (let _0_549 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right _0_549 FStar_Util.fifo_set_elements))
in univnames))))


let maybe_set_tk = (fun ts uu___94_4651 -> (match (uu___94_4651) with
| None -> begin
ts
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange)
in (

let t = (FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t)
in ((FStar_ST.write (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)));
ts;
)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____4692) -> begin
generalized_univ_names
end
| (uu____4696, []) -> begin
explicit_univ_names
end
| uu____4700 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_551 = (let _0_550 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " _0_550))
in ((_0_551), (t.FStar_Syntax_Syntax.pos))))))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames = (gather_free_univnames env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in ((

let uu____4718 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____4718) with
| true -> begin
(let _0_552 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _0_552))
end
| uu____4720 -> begin
()
end));
(

let gen = (gen_univs env univs)
in ((

let uu____4724 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____4724) with
| true -> begin
(let _0_553 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _0_553))
end
| uu____4725 -> begin
()
end));
(

let univs = (check_universe_generalization univnames gen t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs t)
in (let _0_554 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs), (ts)) _0_554))));
));
)))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> (

let uu____4757 = (let _0_555 = (FStar_Util.for_all (fun uu____4762 -> (match (uu____4762) with
| (uu____4767, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _0_555))
in (match (uu____4757) with
| true -> begin
None
end
| uu____4784 -> begin
(

let norm = (fun c -> ((

let uu____4790 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____4790) with
| true -> begin
(let _0_556 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _0_556))
end
| uu____4791 -> begin
()
end));
(

let c = (

let uu____4793 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____4793) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
| uu____4794 -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end))
in ((

let uu____4796 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____4796) with
| true -> begin
(let _0_557 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _0_557))
end
| uu____4797 -> begin
()
end));
c;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _0_558 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _0_558 FStar_Util.set_elements)))
in (

let uu____4864 = (let _0_559 = (FStar_All.pipe_right ecs (FStar_List.map (fun uu____4953 -> (match (uu____4953) with
| (e, c) -> begin
(

let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (

let c = (norm c)
in (

let t = (FStar_Syntax_Util.comp_result c)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let uvt = (FStar_Syntax_Free.uvars t)
in (

let uvs = (gen_uvars uvt)
in ((univs), (((uvs), (e), (c))))))))))
end))))
in (FStar_All.pipe_right _0_559 FStar_List.unzip))
in (match (uu____4864) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in ((

let uu____5082 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5082) with
| true -> begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end
| uu____5085 -> begin
()
end));
(

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun uu____5124 -> (match (uu____5124) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____5181 -> (match (uu____5181) with
| (u, k) -> begin
(

let uu____5201 = (FStar_Unionfind.find u)
in (match (uu____5201) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (uu____5239) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____5247 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let uu____5252 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____5252) with
| (bs, kres) -> begin
(

let a = (let _0_562 = (let _0_561 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_560 -> Some (_0_560)) _0_561))
in (FStar_Syntax_Syntax.new_bv _0_562 kres))
in (

let t = (let _0_564 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_563 = Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (FStar_Syntax_Syntax.mk_Total kres))))
in (FStar_Syntax_Util.abs bs _0_564 _0_563)))
in ((FStar_Syntax_Util.set_uvar u t);
((a), (Some (FStar_Syntax_Syntax.imp_tag)));
)))
end)))
end))
end))))
in (

let uu____5290 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], uu____5308) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e), (c))))
end
| uu____5320 -> begin
(

let uu____5328 = ((e), (c))
in (match (uu____5328) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (

let uu____5340 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c)).FStar_Syntax_Syntax.n
in (match (uu____5340) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____5355 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____5355) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| uu____5365 -> begin
(FStar_Syntax_Util.arrow tvars c)
end))
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _0_565 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_0_565)))))))
end))
end)
in (match (uu____5290) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs));
)))
end)))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> ((

let uu____5412 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5412) with
| true -> begin
(let _0_567 = (let _0_566 = (FStar_List.map (fun uu____5417 -> (match (uu____5417) with
| (lb, uu____5422, uu____5423) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _0_566 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _0_567))
end
| uu____5424 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____5432 -> (match (uu____5432) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____5447 = (let _0_568 = (FStar_All.pipe_right lecs (FStar_List.map (fun uu____5466 -> (match (uu____5466) with
| (uu____5472, e, c) -> begin
((e), (c))
end))))
in (gen env _0_568))
in (match (uu____5447) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____5504 -> (match (uu____5504) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun uu____5548 uu____5549 -> (match (((uu____5548), (uu____5549))) with
| ((l, uu____5582, uu____5583), (us, e, c)) -> begin
((

let uu____5609 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5609) with
| true -> begin
(let _0_572 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _0_571 = (FStar_Syntax_Print.lbname_to_string l)
in (let _0_570 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _0_569 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _0_572 _0_571 _0_570 _0_569)))))
end
| uu____5610 -> begin
()
end));
((l), (us), (e), (c));
)
end)) lecs ecs)
end))
in (FStar_List.map2 (fun univnames uu____5628 -> (match (uu____5628) with
| (l, generalized_univs, t, c) -> begin
(let _0_573 = (check_universe_generalization univnames generalized_univs t)
in ((l), (_0_573), (t), (c)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env t1 t2 -> (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end
| uu____5676 -> begin
(

let uu____5677 = (FStar_TypeChecker_Rel.try_subtype env t1 t2)
in (match (uu____5677) with
| None -> begin
None
end
| Some (f) -> begin
(let _0_575 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_574 -> Some (_0_574)) _0_575))
end))
end))
in (

let is_var = (fun e -> (

let uu____5686 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____5686) with
| FStar_Syntax_Syntax.Tm_name (uu____5687) -> begin
true
end
| uu____5688 -> begin
false
end)))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___136_5710 = x
in {FStar_Syntax_Syntax.ppname = uu___136_5710.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_5710.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| uu____5711 -> begin
(

let uu___137_5712 = e
in (let _0_576 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = uu___137_5712.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _0_576; FStar_Syntax_Syntax.pos = uu___137_5712.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___137_5712.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let uu___138_5719 = env
in (let _0_577 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___138_5719.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___138_5719.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___138_5719.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___138_5719.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___138_5719.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___138_5719.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___138_5719.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___138_5719.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___138_5719.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___138_5719.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___138_5719.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___138_5719.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___138_5719.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___138_5719.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___138_5719.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _0_577; FStar_TypeChecker_Env.is_iface = uu___138_5719.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___138_5719.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___138_5719.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___138_5719.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___138_5719.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___138_5719.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___138_5719.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___138_5719.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____5720 = (check env t1 t2)
in (match (uu____5720) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_579 = (FStar_TypeChecker_Err.expected_expression_of_type env t2 e t1)
in (let _0_578 = (FStar_TypeChecker_Env.get_range env)
in ((_0_579), (_0_578)))))))
end
| Some (g) -> begin
((

let uu____5728 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____5728) with
| true -> begin
(let _0_580 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _0_580))
end
| uu____5729 -> begin
()
end));
(let _0_581 = (decorate e t2)
in ((_0_581), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> ((FStar_TypeChecker_Rel.force_trivial_guard env g);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____5751 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____5751) with
| true -> begin
(let _0_583 = (discharge g)
in (let _0_582 = (lc.FStar_Syntax_Syntax.comp ())
in ((_0_583), (_0_582))))
end
| uu____5756 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _0_586 = (let _0_585 = (let _0_584 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _0_584 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _0_585 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _0_586 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let uu____5764 = (destruct_comp c)
in (match (uu____5764) with
| (u_t, t, wp) -> begin
(

let vc = (let _0_592 = (FStar_TypeChecker_Env.get_range env)
in ((let _0_591 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _0_590 = (let _0_589 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_588 = (let _0_587 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_587)::[])
in (_0_589)::_0_588))
in (FStar_Syntax_Syntax.mk_Tm_app _0_591 _0_590))) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _0_592))
in ((

let uu____5781 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____5781) with
| true -> begin
(let _0_593 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _0_593))
end
| uu____5782 -> begin
()
end));
(

let g = (let _0_594 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _0_594))
in (let _0_596 = (discharge g)
in (let _0_595 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_0_596), (_0_595)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f uu___95_5807 -> (match (uu___95_5807) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, uu____5813))::[] -> begin
(f fst)
end
| uu____5826 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _0_598 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _0_598 (fun _0_597 -> FStar_TypeChecker_Common.NonTrivial (_0_597)))))
in (

let op_or_e = (fun e -> (let _0_600 = (FStar_Syntax_Util.mk_neg (FStar_Syntax_Util.b2t e))
in (FStar_All.pipe_right _0_600 (fun _0_599 -> FStar_TypeChecker_Common.NonTrivial (_0_599)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_601 -> FStar_TypeChecker_Common.NonTrivial (_0_601))))
in (

let op_or_t = (fun t -> (let _0_603 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _0_603 (fun _0_602 -> FStar_TypeChecker_Common.NonTrivial (_0_602)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_604 -> FStar_TypeChecker_Common.NonTrivial (_0_604))))
in (

let short_op_ite = (fun uu___96_5858 -> (match (uu___96_5858) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____5864))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____5879))::[] -> begin
(let _0_606 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _0_606 (fun _0_605 -> FStar_TypeChecker_Common.NonTrivial (_0_605))))
end
| uu____5902 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____5955 = (FStar_Util.find_map table (fun uu____5961 -> (match (uu____5961) with
| (x, mk) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
Some ((mk seen_args))
end
| uu____5974 -> begin
None
end)
end)))
in (match (uu____5955) with
| None -> begin
FStar_TypeChecker_Common.Trivial
end
| Some (g) -> begin
g
end)))
end
| uu____5976 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____5980 = (FStar_Syntax_Util.un_uinst l).FStar_Syntax_Syntax.n
in (match (uu____5980) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| uu____5982 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, uu____6000))::uu____6001 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| uu____6007 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____6011, Some (FStar_Syntax_Syntax.Implicit (uu____6012))))::uu____6013 -> begin
bs
end
| uu____6022 -> begin
(

let uu____6023 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6023) with
| None -> begin
bs
end
| Some (t) -> begin
(

let uu____6026 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____6026) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____6028) -> begin
(

let uu____6039 = (FStar_Util.prefix_until (fun uu___97_6058 -> (match (uu___97_6058) with
| (uu____6062, Some (FStar_Syntax_Syntax.Implicit (uu____6063))) -> begin
false
end
| uu____6065 -> begin
true
end)) bs')
in (match (uu____6039) with
| None -> begin
bs
end
| Some ([], uu____6083, uu____6084) -> begin
bs
end
| Some (imps, uu____6121, uu____6122) -> begin
(

let uu____6159 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____6167 -> (match (uu____6167) with
| (x, uu____6172) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____6159) with
| true -> begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun uu____6195 -> (match (uu____6195) with
| (x, i) -> begin
(let _0_607 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_0_607), (i)))
end))))
in (FStar_List.append imps bs)))
end
| uu____6210 -> begin
bs
end))
end))
end
| uu____6211 -> begin
bs
end))
end))
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 t -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in (match ((((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1)))) with
| true -> begin
e
end
| uu____6229 -> begin
(let _0_608 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t)))))))) _0_608 e.FStar_Syntax_Syntax.pos))
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____6254 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid))
in (match (uu____6254) with
| true -> begin
e
end
| uu____6255 -> begin
(let _0_609 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t)))))))) _0_609 e.FStar_Syntax_Syntax.pos))
end))))


let effect_repr_aux = (fun only_reifiable env c u_c -> (

let uu____6296 = (let _0_610 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _0_610))
in (match (uu____6296) with
| None -> begin
None
end
| Some (ed) -> begin
(

let uu____6304 = (only_reifiable && (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))))
in (match (uu____6304) with
| true -> begin
None
end
| uu____6311 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
None
end
| uu____6317 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____6319 = (let _0_611 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_0_611)))
in (match (uu____6319) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in Some ((let _0_614 = (FStar_TypeChecker_Env.get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_613 = (let _0_612 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_0_612)::(wp)::[])
in ((repr), (_0_613)))))) None _0_614))))
end)))
end)
end))
end)))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (Prims.raise (FStar_Errors.Error ((let _0_616 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _0_615 = (FStar_TypeChecker_Env.get_range env)
in ((_0_616), (_0_615))))))))
in (

let uu____6404 = (let _0_617 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _0_617 u_c))
in (match (uu____6404) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____6432 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____6432) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(let _0_618 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _0_618));
)
end
| uu____6434 -> begin
()
end));
(

let fv = (let _0_619 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _0_619 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]), ([])))
in (let _0_620 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv))) None FStar_Range.dummyRange)
in ((sig_ctx), (_0_620)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___98_6466 -> (match (uu___98_6466) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____6467 -> begin
false
end))
in (

let reducibility = (fun uu___99_6471 -> (match (uu___99_6471) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____6472 -> begin
false
end))
in (

let assumption = (fun uu___100_6476 -> (match (uu___100_6476) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| uu____6477 -> begin
false
end))
in (

let reification = (fun uu___101_6481 -> (match (uu___101_6481) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| uu____6483 -> begin
false
end))
in (

let inferred = (fun uu___102_6487 -> (match (uu___102_6487) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| uu____6492 -> begin
false
end))
in (

let has_eq = (fun uu___103_6496 -> (match (uu___103_6496) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| uu____6497 -> begin
false
end))
in (

let quals_combo_ok = (fun quals q -> (match (q) with
| FStar_Syntax_Syntax.Assumption -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (inferred x)) || (visibility x)) || (assumption x)) || (env.FStar_TypeChecker_Env.is_iface && (x = FStar_Syntax_Syntax.Inline_for_extraction))))))
end
| FStar_Syntax_Syntax.New -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((x = q) || (inferred x)) || (visibility x)) || (assumption x)))))
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (visibility x)) || (reducibility x)) || (reification x)) || (inferred x)) || (env.FStar_TypeChecker_Env.is_iface && (x = FStar_Syntax_Syntax.Assumption))))))
end
| (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (x = FStar_Syntax_Syntax.Abstract)) || (x = FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.TotalEffect -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((x = q) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Logic -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) || (inferred x)) || (visibility x)) || (reducibility x)))))
end
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (x = FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____6522 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____6525 = (let _0_621 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___104_6527 -> (match (uu___104_6527) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____6528 -> begin
false
end))))
in (FStar_All.pipe_right _0_621 Prims.op_Negation))
in (match (uu____6525) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (Prims.raise (FStar_Errors.Error ((let _0_623 = (let _0_622 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" _0_622 msg))
in ((_0_623), (r)))))))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun uu____6545 -> (err' ""))
in ((match (((FStar_List.length quals) <> (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____6551 -> begin
()
end);
(

let uu____6553 = (not ((FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))))
in (match (uu____6553) with
| true -> begin
(err "ill-formed combination")
end
| uu____6555 -> begin
()
end));
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____6557), uu____6558, uu____6559, uu____6560, uu____6561) -> begin
((

let uu____6574 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____6574) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____6576 -> begin
()
end));
(

let uu____6577 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____6577) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____6580 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____6581) -> begin
(

let uu____6589 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))))
in (match (uu____6589) with
| true -> begin
(err' ())
end
| uu____6592 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____6593) -> begin
(

let uu____6600 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____6600) with
| true -> begin
(err' ())
end
| uu____6602 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____6603) -> begin
(

let uu____6609 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption)))))))
in (match (uu____6609) with
| true -> begin
(err' ())
end
| uu____6612 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____6613) -> begin
(

let uu____6616 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))))
in (match (uu____6616) with
| true -> begin
(err' ())
end
| uu____6619 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____6620) -> begin
(

let uu____6623 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))))
in (match (uu____6623) with
| true -> begin
(err' ())
end
| uu____6626 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____6627) -> begin
(

let uu____6637 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))))
in (match (uu____6637) with
| true -> begin
(err' ())
end
| uu____6640 -> begin
()
end))
end
| uu____6641 -> begin
()
end);
))))))
end
| uu____6642 -> begin
()
end)))))))))))


let mk_discriminator_and_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid uvs inductive_tps indices fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (

let inst_univs = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) uvs)
in (

let tps = inductive_tps
in (

let arg_typ = (

let inst_tc = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_624 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None))
in ((_0_624), (inst_univs)))))) None p)
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____6723 -> (match (uu____6723) with
| (x, imp) -> begin
(let _0_625 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_0_625), (imp)))
end))))
in ((FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p)))
in (

let unrefined_arg_binder = (FStar_Syntax_Syntax.mk_binder (projectee arg_typ))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____6736 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational None)
in (let _0_630 = (FStar_Syntax_Util.b2t ((let _0_629 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (let _0_628 = (let _0_627 = (let _0_626 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_626))
in (_0_627)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_629 _0_628))) None p))
in (FStar_Syntax_Util.refine x _0_630)))
in (FStar_Syntax_Syntax.mk_binder (

let uu___139_6749 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___139_6749.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___139_6749.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _0_631 = (FStar_List.map (fun uu____6767 -> (match (uu____6767) with
| (x, uu____6774) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append _0_631 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____6795 -> (match (uu____6795) with
| (x, uu____6802) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((fvq <> FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____6807 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((let _0_632 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_632)) || (FStar_Options.dont_gen_projectors (FStar_TypeChecker_Env.current_module env).FStar_Ident.str))
in (

let quals = (let _0_635 = (let _0_634 = (

let uu____6815 = (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit))
in (match (uu____6815) with
| true -> begin
(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____6817 -> begin
[]
end))
in (let _0_633 = (FStar_List.filter (fun uu___105_6818 -> (match (uu___105_6818) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____6819 -> begin
false
end)) iquals)
in (FStar_List.append _0_634 _0_633)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::[]
end
| uu____6814 -> begin
[]
end)) _0_635))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)))
in (let _0_636 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _0_636)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid discriminator_name))))
in ((

let uu____6833 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____6833) with
| true -> begin
(let _0_637 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" _0_637))
end
| uu____6834 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____6836 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Const.exp_true_bool
end
| uu____6842 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____6865 -> (match (uu____6865) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(let _0_639 = (pos (FStar_Syntax_Syntax.Pat_dot_term ((let _0_638 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_0_638), (FStar_Syntax_Syntax.tun))))))
in ((_0_639), (b)))
end
| uu____6883 -> begin
(let _0_640 = (pos (FStar_Syntax_Syntax.Pat_wild ((FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun))))
in ((_0_640), (b)))
end))
end))))
in (

let pat_true = (let _0_642 = (pos (FStar_Syntax_Syntax.Pat_cons ((let _0_641 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_0_641), (arg_pats))))))
in ((_0_642), (None), (FStar_Syntax_Const.exp_true_bool)))
in (

let pat_false = (let _0_643 = (pos (FStar_Syntax_Syntax.Pat_wild ((FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun))))
in ((_0_643), (None), (FStar_Syntax_Const.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst unrefined_arg_binder))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((let _0_647 = (let _0_646 = (FStar_Syntax_Util.branch pat_true)
in (let _0_645 = (let _0_644 = (FStar_Syntax_Util.branch pat_false)
in (_0_644)::[])
in (_0_646)::_0_645))
in ((arg_exp), (_0_647)))))) None p)))))
end)
in (

let dd = (

let uu____6942 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6942) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____6944 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____6952 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (let _0_649 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv discriminator_name dd None))
in (let _0_648 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _0_649; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _0_648}))
in (

let impl = FStar_Syntax_Syntax.Sig_let ((let _0_652 = (let _0_651 = (let _0_650 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _0_650 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_0_651)::[])
in ((((false), ((lb)::[]))), (p), (_0_652), (quals), ([]))))
in ((

let uu____6970 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____6970) with
| true -> begin
(let _0_653 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" _0_653))
end
| uu____6971 -> begin
()
end));
(decl)::(impl)::[];
)))))))
end);
))))))))
end)
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6990 -> (match (uu____6990) with
| (a, uu____6994) -> begin
(

let uu____6995 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____6995) with
| (field_name, uu____6999) -> begin
(

let field_proj_tm = (let _0_654 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_654 inst_univs))
in (

let proj = ((FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[])) None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (let _0_675 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7025 -> (match (uu____7025) with
| (x, uu____7030) -> begin
(

let p = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____7032 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____7032) with
| (field_name, uu____7037) -> begin
(

let t = (let _0_656 = (let _0_655 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort))
in (FStar_Syntax_Util.arrow binders _0_655))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _0_656))
in (

let only_decl = (((let _0_657 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_657)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (FStar_Options.dont_gen_projectors (FStar_TypeChecker_Env.current_module env).FStar_Ident.str))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(let _0_658 = (FStar_List.filter (fun uu___106_7049 -> (match (uu___106_7049) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____7050 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_0_658)
end
| uu____7051 -> begin
q
end))
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___107_7058 -> (match (uu___107_7058) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____7059 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in ((

let uu____7063 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7063) with
| true -> begin
(let _0_659 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" _0_659))
end
| uu____7064 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____7066 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____7090 -> (match (uu____7090) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match (((i + ntps) = j)) with
| true -> begin
(let _0_660 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_0_660), (b)))
end
| uu____7108 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(let _0_662 = (pos (FStar_Syntax_Syntax.Pat_dot_term ((let _0_661 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_0_661), (FStar_Syntax_Syntax.tun))))))
in ((_0_662), (b)))
end
| uu____7117 -> begin
(let _0_663 = (pos (FStar_Syntax_Syntax.Pat_wild ((FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun))))
in ((_0_663), (b)))
end)
end))
end))))
in (

let pat = (let _0_666 = (pos (FStar_Syntax_Syntax.Pat_cons ((let _0_664 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_0_664), (arg_pats))))))
in (let _0_665 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_0_666), (None), (_0_665))))
in (

let body = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((let _0_668 = (let _0_667 = (FStar_Syntax_Util.branch pat)
in (_0_667)::[])
in ((arg_exp), (_0_668)))))) None p)
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let dd = (

let uu____7160 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____7160) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____7162 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____7164 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (let _0_670 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv field_name dd None))
in (let _0_669 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _0_670; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _0_669}))
in (

let impl = FStar_Syntax_Syntax.Sig_let ((let _0_673 = (let _0_672 = (let _0_671 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _0_671 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_0_672)::[])
in ((((false), ((lb)::[]))), (p), (_0_673), (quals), ([]))))
in ((

let uu____7182 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7182) with
| true -> begin
(let _0_674 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" _0_674))
end
| uu____7183 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____7185 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
)))))))
end)))
end))))
in (FStar_All.pipe_right _0_675 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, quals, uu____7210, r) when (not ((FStar_Ident.lid_equals constr_lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____7216 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____7216) with
| (univ_opening, uvs) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____7229 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____7229) with
| (formals, uu____7239) -> begin
(

let uu____7250 = (

let tps_opt = (FStar_Util.find_map tcs (fun se -> (

let uu____7263 = (let _0_676 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals typ_lid _0_676))
in (match (uu____7263) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7272, uvs', tps, typ0, uu____7276, constrs, uu____7278, uu____7279) -> begin
Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____7293 -> begin
(failwith "Impossible")
end)
end
| uu____7298 -> begin
None
end))))
in (match (tps_opt) with
| Some (x) -> begin
x
end
| None -> begin
(match ((FStar_Ident.lid_equals typ_lid FStar_Syntax_Const.exn_lid)) with
| true -> begin
(([]), (FStar_Syntax_Util.ktype0), (true))
end
| uu____7325 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____7250) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ0 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____7335 = (FStar_Syntax_Util.arrow_formals typ0)
in (match (uu____7335) with
| (indices, uu____7345) -> begin
(

let refine_domain = (

let uu____7357 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___108_7359 -> (match (uu___108_7359) with
| FStar_Syntax_Syntax.RecordConstructor (uu____7360) -> begin
true
end
| uu____7365 -> begin
false
end))))
in (match (uu____7357) with
| true -> begin
false
end
| uu____7366 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___109_7372 -> (match (uu___109_7372) with
| FStar_Syntax_Syntax.RecordConstructor (uu____7374, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____7381 -> begin
None
end))
in (

let uu____7382 = (FStar_Util.find_map quals filter_records)
in (match (uu____7382) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)))
in (

let iquals = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____7388 -> begin
iquals
end)
in (

let fields = (

let uu____7390 = (FStar_Util.first_N n_typars formals)
in (match (uu____7390) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____7421 uu____7422 -> (match (((uu____7421), (uu____7422))) with
| ((x, uu____7432), (x', uu____7434)) -> begin
FStar_Syntax_Syntax.NT ((let _0_677 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (_0_677))))
end)) imp_tps inductive_tps)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals fv_qual refine_domain env typ_lid constr_lid uvs inductive_tps indices fields)))))
end))))
end))
end)))
end))
end
| uu____7439 -> begin
[]
end))




