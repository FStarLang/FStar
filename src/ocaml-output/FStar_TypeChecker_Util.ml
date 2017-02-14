
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _0_238 = (FStar_TypeChecker_Env.get_range env)
in (let _0_237 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.report _0_238 _0_237))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____15 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____15) with
| FStar_Syntax_Syntax.Tm_type (uu____16) -> begin
true
end
| uu____17 -> begin
false
end)))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env -> (let _0_239 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _0_239 (FStar_List.filter (fun uu____29 -> (match (uu____29) with
| (x, uu____33) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = (

let uu____43 = ((FStar_Options.full_context_dependency ()) || (let _0_240 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_240)))
in (match (uu____43) with
| true -> begin
(FStar_TypeChecker_Env.all_binders env)
end
| uu____44 -> begin
(t_binders env)
end))
in (let _0_241 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _0_241 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (Prims.fst (new_uvar_aux env k)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___91_53 -> (match (uu___91_53) with
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

let uu___111_170 = FStar_TypeChecker_Rel.trivial_guard
in (let _0_244 = (let _0_243 = (let _0_242 = (as_uvar u)
in ((reason), (env), (_0_242), (t), (k), (r)))
in (_0_243)::[])
in {FStar_TypeChecker_Env.guard_f = uu___111_170.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___111_170.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___111_170.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _0_244}))
in (let _0_247 = (let _0_246 = (let _0_245 = (as_uvar u)
in ((_0_245), (r)))
in (_0_246)::[])
in ((t), (_0_247), (g))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____200 = (not ((FStar_Util.set_is_empty uvs)))
in (match (uu____200) with
| true -> begin
(

let us = (let _0_249 = (let _0_248 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun uu____211 -> (match (uu____211) with
| (x, uu____219) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _0_248))
in (FStar_All.pipe_right _0_249 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(let _0_251 = (let _0_250 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _0_250))
in (FStar_Errors.report r _0_251));
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
(failwith (let _0_253 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _0_252 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _0_253 _0_252))))
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

let t = (let _0_254 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _0_254 Prims.fst))
in (((

let uu___112_332 = a
in {FStar_Syntax_Syntax.ppname = uu___112_332.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_332.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
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

let uu____560 = (FStar_Options.ml_ish ())
in (match (uu____560) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r)
end
| uu____561 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t = (FStar_Syntax_Util.arrow bs c)
in ((

let uu____567 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____567) with
| true -> begin
(let _0_257 = (FStar_Range.string_of_range r)
in (let _0_256 = (FStar_Syntax_Print.term_to_string t)
in (let _0_255 = (FStar_Util.string_of_bool must_check_ty)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" _0_257 _0_256 _0_255))))
end
| uu____568 -> begin
()
end));
((FStar_Util.Inl (t)), (must_check_ty));
)))
end))
end))
end
| uu____575 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end
| uu____582 -> begin
(let _0_259 = FStar_Util.Inl ((let _0_258 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _0_258 Prims.fst)))
in ((_0_259), (false)))
end)
end)))
in (

let uu____587 = (let _0_260 = (t_binders env)
in (aux false _0_260 e))
in (match (uu____587) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(

let uu____608 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____608) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____611 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_262 = (let _0_261 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _0_261))
in ((_0_262), (rng))))))
end))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end)))));
)
end
| uu____618 -> begin
(

let uu____619 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (uu____619) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____702) -> begin
(

let uu____707 = (FStar_Syntax_Util.type_u ())
in (match (uu____707) with
| (k, uu____720) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let uu___113_723 = x
in {FStar_Syntax_Syntax.ppname = uu___113_723.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___113_723.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____724 = (let _0_263 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _0_263 t))
in (match (uu____724) with
| (e, u) -> begin
(

let p = (

let uu___114_741 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = uu___114_741.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___114_741.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____748 = (FStar_Syntax_Util.type_u ())
in (match (uu____748) with
| (t, uu____761) -> begin
(

let x = (

let uu___115_763 = x
in (let _0_264 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = uu___115_763.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_763.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_264}))
in (

let env = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env x)
end
| uu____765 -> begin
env
end)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x))) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ([]), ((x)::[]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____783 = (FStar_Syntax_Util.type_u ())
in (match (uu____783) with
| (t, uu____796) -> begin
(

let x = (

let uu___116_798 = x
in (let _0_265 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = uu___116_798.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_798.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_265}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x))) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____828 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____884 uu____885 -> (match (((uu____884), (uu____885))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let uu____984 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (uu____984) with
| (b', a', w', env, te, pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1023 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (((b')::b), ((a')::a), ((w')::w), (env), ((arg)::args), ((((pat), (imp)))::pats)))
end))
end)) (([]), ([]), ([]), (env), ([]), ([]))))
in (match (uu____828) with
| (b, a, w, env, args, pats) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((let _0_268 = ((let _0_267 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _0_266 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _0_267 _0_266))) None p.FStar_Syntax_Syntax.p)
in ((_0_268), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))) None p.FStar_Syntax_Syntax.p)
in (let _0_271 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _0_270 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _0_269 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_0_271), (_0_270), (_0_269), (env), (e), ((

let uu___117_1129 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___117_1129.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___117_1129.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (uu____1135) -> begin
(failwith "impossible")
end))
in (

let rec elaborate_pat = (fun env p -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end
| uu____1175 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats = (FStar_List.map (fun uu____1204 -> (match (uu____1204) with
| (p, imp) -> begin
(let _0_272 = (elaborate_pat env p)
in ((_0_272), (imp)))
end)) pats)
in (

let uu____1221 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1221) with
| (uu____1230, t) -> begin
(

let uu____1232 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1232) with
| (f, uu____1243) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (uu____1318)::uu____1319) -> begin
(Prims.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((uu____1354)::uu____1355, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____1395 -> (match (uu____1395) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _0_273 = Some ((FStar_Syntax_Syntax.range_of_bv t))
in (FStar_Syntax_Syntax.new_bv _0_273 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _0_274 = (maybe_dot inaccessible a r)
in ((_0_274), (true)))))
end
| uu____1420 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_276 = (let _0_275 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _0_275))
in ((_0_276), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (uu____1472, Some (FStar_Syntax_Syntax.Implicit (uu____1473))) when p_imp -> begin
(let _0_277 = (aux formals' pats')
in (((p), (true)))::_0_277)
end
| (uu____1481, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _0_278 = (aux formals' pats)
in (((p), (true)))::_0_278)))
end
| (uu____1498, imp) -> begin
(let _0_281 = (let _0_279 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_0_279)))
in (let _0_280 = (aux formals' pats')
in (_0_281)::_0_280))
end)
end))
in (

let uu___118_1508 = p
in (let _0_283 = FStar_Syntax_Syntax.Pat_cons ((let _0_282 = (aux f pats)
in ((fv), (_0_282))))
in {FStar_Syntax_Syntax.v = _0_283; FStar_Syntax_Syntax.ty = uu___118_1508.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___118_1508.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____1516 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let uu____1542 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (uu____1542) with
| (b, a, w, env, arg, p) -> begin
(

let uu____1572 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____1572) with
| Some (x) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_284 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in ((_0_284), (p.FStar_Syntax_Syntax.p))))))
end
| uu____1593 -> begin
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

let uu____1636 = (one_pat false env q)
in (match (uu____1636) with
| (b, a, uu____1652, te, q) -> begin
(

let uu____1661 = (FStar_List.fold_right (fun p uu____1677 -> (match (uu____1677) with
| (w, args, pats) -> begin
(

let uu____1701 = (one_pat false env p)
in (match (uu____1701) with
| (b', a', w', arg, p) -> begin
(

let uu____1727 = (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a')))
in (match (uu____1727) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_286 = (FStar_TypeChecker_Err.disjunctive_pattern_vars a a')
in (let _0_285 = (FStar_TypeChecker_Env.get_range env)
in ((_0_286), (_0_285)))))))
end
| uu____1740 -> begin
(let _0_288 = (let _0_287 = (FStar_Syntax_Syntax.as_arg arg)
in (_0_287)::args)
in (((FStar_List.append w' w)), (_0_288), ((p)::pats)))
end))
end))
end)) pats (([]), ([]), ([])))
in (match (uu____1661) with
| (w, args, pats) -> begin
(let _0_290 = (let _0_289 = (FStar_Syntax_Syntax.as_arg te)
in (_0_289)::args)
in (((FStar_List.append b w)), (_0_290), ((

let uu___119_1765 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = uu___119_1765.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___119_1765.FStar_Syntax_Syntax.p}))))
end))
end))
end
| uu____1766 -> begin
(

let uu____1767 = (one_pat true env p)
in (match (uu____1767) with
| (b, uu____1782, uu____1783, arg, p) -> begin
(let _0_292 = (let _0_291 = (FStar_Syntax_Syntax.as_arg arg)
in (_0_291)::[])
in ((b), (_0_292), (p)))
end))
end))
in (

let uu____1794 = (top_level_pat_as_args env p)
in (match (uu____1794) with
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
| (uu____1865, FStar_Syntax_Syntax.Tm_uinst (e, uu____1867)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____1872), FStar_Syntax_Syntax.Tm_constant (uu____1873)) -> begin
(let _0_293 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _0_293))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(failwith (let _0_295 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_294 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _0_295 _0_294))))
end
| uu____1877 -> begin
()
end);
(

let uu____1879 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____1879) with
| true -> begin
(let _0_297 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_296 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _0_297 _0_296)))
end
| uu____1880 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___120_1883 = x
in {FStar_Syntax_Syntax.ppname = uu___120_1883.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_1883.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____1887 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____1887) with
| true -> begin
(failwith (let _0_299 = (FStar_Syntax_Print.bv_to_string x)
in (let _0_298 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _0_299 _0_298))))
end
| uu____1888 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___121_1891 = x
in {FStar_Syntax_Syntax.ppname = uu___121_1891.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_1891.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____1893), uu____1894) -> begin
(

let s = (force_sort e)
in (

let x = (

let uu___122_1903 = x
in {FStar_Syntax_Syntax.ppname = uu___122_1903.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___122_1903.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____1916 = (not ((FStar_Syntax_Syntax.fv_eq fv fv')))
in (match (uu____1916) with
| true -> begin
(failwith (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str))
end
| uu____1925 -> begin
()
end));
(let _0_300 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _0_300));
)
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
((

let uu____1996 = (let _0_301 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _0_301 Prims.op_Negation))
in (match (uu____1996) with
| true -> begin
(failwith (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str))
end
| uu____2005 -> begin
()
end));
(

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _0_302 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _0_302))
end
| ((arg)::args, ((argpat, uu____2096))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____2146)) -> begin
(

let x = (let _0_303 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _0_303))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), uu____2175) -> begin
(

let pat = (let _0_305 = (aux argpat e)
in (let _0_304 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_0_305), (_0_304))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| uu____2192 -> begin
(failwith (let _0_307 = (FStar_Syntax_Print.pat_to_string p)
in (let _0_306 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _0_307 _0_306))))
end))
in (match_args [] args argpats)));
)
end
| uu____2212 -> begin
(failwith (let _0_311 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _0_310 = (FStar_Syntax_Print.pat_to_string qq)
in (let _0_309 = (let _0_308 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _0_308 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _0_311 _0_310 _0_309)))))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), uu____2220) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (uu____2236, (e)::[]) -> begin
(aux p e)
end
| uu____2239 -> begin
(failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> ((FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____2276 -> (match (uu____2276) with
| (p, i) -> begin
(

let uu____2286 = (decorated_pattern_as_term p)
in (match (uu____2286) with
| (vars, te) -> begin
(let _0_313 = (let _0_312 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_0_312)))
in ((vars), (_0_313)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____2305) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _0_314 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_0_314)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _0_315 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_0_315)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2328 = (let _0_316 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _0_316 FStar_List.unzip))
in (match (uu____2328) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _0_318 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_317 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_0_317), (args))))))
in ((vars), (_0_318))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____2415))::[] -> begin
wp
end
| uu____2428 -> begin
(failwith (let _0_320 = (let _0_319 = (FStar_List.map (fun uu____2439 -> (match (uu____2439) with
| (x, uu____2443) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _0_319 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _0_320)))
end)
in (let _0_321 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_0_321), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____2471 = (destruct_comp c)
in (match (uu____2471) with
| (u, uu____2476, wp) -> begin
(let _0_323 = (let _0_322 = (FStar_Syntax_Syntax.as_arg (lift c.FStar_Syntax_Syntax.result_typ wp))
in (_0_322)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _0_323; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____2487 = (let _0_325 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _0_324 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _0_325 _0_324)))
in (match (uu____2487) with
| (m, uu____2492, uu____2493) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____2503 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____2503) with
| true -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| uu____2504 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (

let uu____2528 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (uu____2528) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____2558 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____2558) with
| (a, kwp) -> begin
(let _0_327 = (destruct_comp m1)
in (let _0_326 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_0_327), (_0_326))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (FStar_Syntax_Syntax.mk_Comp (let _0_329 = (let _0_328 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_328)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _0_329; FStar_Syntax_Syntax.flags = flags})))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (match ((FStar_Ident.lid_equals mname FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (Some (u_result)))
end
| uu____2647 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let uu___123_2654 = lc
in (let _0_331 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___123_2654.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _0_331; FStar_Syntax_Syntax.cflags = uu___123_2654.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2655 -> (let _0_330 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _0_330)))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2659 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2659) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2660) -> begin
true
end
| uu____2668 -> begin
false
end)))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = (

let uu____2679 = (let _0_332 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _0_332))
in (match (uu____2679) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____2680 -> begin
(

let m = (FStar_Util.must (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid))
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (

let uu____2684 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2684) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____2685 -> begin
(

let uu____2686 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (uu____2686) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (let _0_338 = ((let _0_337 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _0_336 = (let _0_335 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_334 = (let _0_333 = (FStar_Syntax_Syntax.as_arg v)
in (_0_333)::[])
in (_0_335)::_0_334))
in (FStar_Syntax_Syntax.mk_Tm_app _0_337 _0_336))) (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _0_338)))
end))
end))
in ((mk_comp m) u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
in ((

let uu____2699 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____2699) with
| true -> begin
(let _0_341 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _0_340 = (FStar_Syntax_Print.term_to_string v)
in (let _0_339 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _0_341 _0_340 _0_339))))
end
| uu____2700 -> begin
()
end));
c;
)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____2716 -> (match (uu____2716) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc1 lc2)
in ((

let uu____2726 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2726) with
| true -> begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _0_344 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _0_343 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _0_342 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _0_344 _0_343 bstr _0_342)))))
end
| uu____2730 -> begin
()
end));
(

let bind_it = (fun uu____2734 -> (

let uu____2735 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2735) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc2.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc2.FStar_Syntax_Syntax.res_typ []))
end
| uu____2737 -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in ((

let uu____2745 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____2745) with
| true -> begin
(let _0_349 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _0_348 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _0_347 = (FStar_Syntax_Print.comp_to_string c1)
in (let _0_346 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _0_345 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _0_349 _0_348 _0_347 _0_346 _0_345))))))
end
| uu____2747 -> begin
()
end));
(

let try_simplify = (fun uu____2754 -> (

let aux = (fun uu____2763 -> (

let uu____2764 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____2764) with
| true -> begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (uu____2781) -> begin
(

let uu____2782 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____2782) with
| true -> begin
Some (((c2), ("trivial ml")))
end
| uu____2794 -> begin
None
end))
end)
end
| uu____2799 -> begin
(

let uu____2800 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____2800) with
| true -> begin
Some (((c2), ("both ml")))
end
| uu____2812 -> begin
None
end))
end)))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
Some ((let _0_350 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_0_350), (reason))))
end
| uu____2835 -> begin
(aux ())
end))
in (

let uu____2840 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____2840) with
| true -> begin
(subst_c2 "both total")
end
| uu____2844 -> begin
(

let uu____2845 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____2845) with
| true -> begin
Some ((let _0_351 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_0_351), ("both gtot"))))
end
| uu____2851 -> begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
(

let uu____2861 = ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x))))
in (match (uu____2861) with
| true -> begin
(subst_c2 "substituted e")
end
| uu____2865 -> begin
(aux ())
end))
end
| uu____2866 -> begin
(aux ())
end)
end))
end)))))
in (

let uu____2871 = (try_simplify ())
in (match (uu____2871) with
| Some (c, reason) -> begin
c
end
| None -> begin
(

let uu____2881 = (lift_and_destruct env c1 c2)
in (match (uu____2881) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _0_352 = (FStar_Syntax_Syntax.null_binder t1)
in (_0_352)::[])
end
| Some (x) -> begin
(let _0_353 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_353)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)))) None r1)
in (

let wp_args = (let _0_362 = (FStar_Syntax_Syntax.as_arg r1)
in (let _0_361 = (let _0_360 = (FStar_Syntax_Syntax.as_arg t1)
in (let _0_359 = (let _0_358 = (FStar_Syntax_Syntax.as_arg t2)
in (let _0_357 = (let _0_356 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _0_355 = (let _0_354 = (FStar_Syntax_Syntax.as_arg (mk_lam wp2))
in (_0_354)::[])
in (_0_356)::_0_355))
in (_0_358)::_0_357))
in (_0_360)::_0_359))
in (_0_362)::_0_361))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = ((let _0_363 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _0_363 wp_args)) None t2.FStar_Syntax_Syntax.pos)
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

let uu____2994 = (let _0_364 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _0_364))
in (match (uu____2994) with
| true -> begin
f
end
| uu____2995 -> begin
(let _0_365 = (reason ())
in (label _0_365 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___124_3006 = g
in (let _0_366 = FStar_TypeChecker_Common.NonTrivial ((label reason r f))
in {FStar_TypeChecker_Env.guard_f = _0_366; FStar_TypeChecker_Env.deferred = uu___124_3006.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___124_3006.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___124_3006.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____3016 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____3033 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3037 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3037) with
| true -> begin
c
end
| uu____3040 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____3044 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3044) with
| true -> begin
c
end
| uu____3047 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3049 = (destruct_comp c)
in (match (uu____3049) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = ((let _0_373 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _0_372 = (let _0_371 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_370 = (let _0_369 = (FStar_Syntax_Syntax.as_arg f)
in (let _0_368 = (let _0_367 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_367)::[])
in (_0_369)::_0_368))
in (_0_371)::_0_370))
in (FStar_Syntax_Syntax.mk_Tm_app _0_373 _0_372))) None wp.FStar_Syntax_Syntax.pos)
in ((mk_comp md) u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end))
end)
end))))
in (

let uu___125_3066 = lc
in {FStar_Syntax_Syntax.eff_name = uu___125_3066.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___125_3066.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___125_3066.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> (

let uu____3093 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____3093) with
| true -> begin
((lc), (g0))
end
| uu____3096 -> begin
((

let uu____3098 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3098) with
| true -> begin
(let _0_375 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _0_374 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _0_375 _0_374)))
end
| uu____3099 -> begin
()
end));
(

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___92_3104 -> (match (uu___92_3104) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| uu____3106 -> begin
[]
end))))
in (

let strengthen = (fun uu____3112 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____3118 -> begin
(

let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____3120 = (FStar_TypeChecker_Rel.guard_form g0)
in (match (uu____3120) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c = (

let uu____3127 = ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c))))
in (match (uu____3127) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (

let xret = (let _0_377 = (let _0_376 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _0_376))
in (FStar_Syntax_Util.comp_set_flags _0_377 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end
| uu____3136 -> begin
c
end))
in ((

let uu____3138 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3138) with
| true -> begin
(let _0_379 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _0_378 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _0_379 _0_378)))
end
| uu____3139 -> begin
()
end));
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3141 = (destruct_comp c)
in (match (uu____3141) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = ((let _0_388 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _0_387 = (let _0_386 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_385 = (let _0_384 = (let _0_381 = (let _0_380 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _0_380 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_381))
in (let _0_383 = (let _0_382 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_382)::[])
in (_0_384)::_0_383))
in (_0_386)::_0_385))
in (FStar_Syntax_Syntax.mk_Tm_app _0_388 _0_387))) None wp.FStar_Syntax_Syntax.pos)
in ((

let uu____3159 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3159) with
| true -> begin
(let _0_389 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _0_389))
end
| uu____3160 -> begin
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
in (let _0_393 = (

let uu___126_3162 = lc
in (let _0_392 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _0_391 = (

let uu____3163 = ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _0_390 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _0_390)))
in (match (uu____3163) with
| true -> begin
flags
end
| uu____3165 -> begin
[]
end))
in {FStar_Syntax_Syntax.eff_name = _0_392; FStar_Syntax_Syntax.res_typ = uu___126_3162.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _0_391; FStar_Syntax_Syntax.comp = strengthen})))
in ((_0_393), ((

let uu___127_3166 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___127_3166.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___127_3166.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___127_3166.FStar_TypeChecker_Env.implicits}))))));
)
end)))


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let uu____3181 = (let _0_395 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _0_394 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_0_395), (_0_394))))
in (match (uu____3181) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = ((let _0_400 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _0_399 = (let _0_398 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_397 = (let _0_396 = (FStar_Syntax_Syntax.as_arg yexp)
in (_0_396)::[])
in (_0_398)::_0_397))
in (FStar_Syntax_Syntax.mk_Tm_app _0_400 _0_399))) None res_t.FStar_Syntax_Syntax.pos)
in (

let x_eq_y_yret = ((let _0_408 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _0_407 = (let _0_406 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_405 = (let _0_404 = (let _0_401 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_401))
in (let _0_403 = (let _0_402 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_0_402)::[])
in (_0_404)::_0_403))
in (_0_406)::_0_405))
in (FStar_Syntax_Syntax.mk_Tm_app _0_408 _0_407))) None res_t.FStar_Syntax_Syntax.pos)
in (

let forall_y_x_eq_y_yret = ((let _0_418 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _0_417 = (let _0_416 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_415 = (let _0_414 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_413 = (let _0_412 = (let _0_411 = (let _0_410 = (let _0_409 = (FStar_Syntax_Syntax.mk_binder y)
in (_0_409)::[])
in (FStar_Syntax_Util.abs _0_410 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_411))
in (_0_412)::[])
in (_0_414)::_0_413))
in (_0_416)::_0_415))
in (FStar_Syntax_Syntax.mk_Tm_app _0_418 _0_417))) None res_t.FStar_Syntax_Syntax.pos)
in (

let lc2 = ((mk_comp md_pure) u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _0_419 = (FStar_TypeChecker_Env.get_range env)
in (bind _0_419 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun uu____3238 -> (

let uu____3239 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3239) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end
| uu____3241 -> begin
(

let uu____3242 = (let _0_421 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _0_420 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _0_421 _0_420)))
in (match (uu____3242) with
| ((md, uu____3256, uu____3257), (u_res_t, res_t, wp_then), (uu____3261, uu____3262, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _0_431 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in ((let _0_430 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _0_429 = (let _0_428 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_427 = (let _0_426 = (FStar_Syntax_Syntax.as_arg g)
in (let _0_425 = (let _0_424 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _0_423 = (let _0_422 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_0_422)::[])
in (_0_424)::_0_423))
in (_0_426)::_0_425))
in (_0_428)::_0_427))
in (FStar_Syntax_Syntax.mk_Tm_app _0_430 _0_429))) None _0_431)))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let uu____3298 = (let _0_432 = (FStar_Options.split_cases ())
in (_0_432 > (Prims.parse_int "0")))
in (match (uu____3298) with
| true -> begin
(

let comp = ((mk_comp md) u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end
| uu____3300 -> begin
(

let wp = ((let _0_437 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _0_436 = (let _0_435 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_434 = (let _0_433 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_433)::[])
in (_0_435)::_0_434))
in (FStar_Syntax_Syntax.mk_Tm_app _0_437 _0_436))) None wp.FStar_Syntax_Syntax.pos)
in ((mk_comp md) u_res_t res_t wp []))
end))))
end))
end)))
in (let _0_438 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _0_438; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _0_440 = (let _0_439 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _0_439))
in (FStar_Syntax_Syntax.fvar _0_440 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____3333 -> (match (uu____3333) with
| (uu____3336, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun uu____3341 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____3343 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3343) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____3344 -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _0_450 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in ((let _0_449 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _0_448 = (let _0_447 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_446 = (let _0_445 = (FStar_Syntax_Syntax.as_arg g)
in (let _0_444 = (let _0_443 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _0_442 = (let _0_441 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_0_441)::[])
in (_0_443)::_0_442))
in (_0_445)::_0_444))
in (_0_447)::_0_446))
in (FStar_Syntax_Syntax.mk_Tm_app _0_449 _0_448))) None _0_450)))
in (

let default_case = (

let post_k = (let _0_453 = (let _0_451 = (FStar_Syntax_Syntax.null_binder res_t)
in (_0_451)::[])
in (let _0_452 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _0_453 _0_452)))
in (

let kwp = (let _0_456 = (let _0_454 = (FStar_Syntax_Syntax.null_binder post_k)
in (_0_454)::[])
in (let _0_455 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _0_456 _0_455)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _0_462 = (let _0_457 = (FStar_Syntax_Syntax.mk_binder post)
in (_0_457)::[])
in (let _0_461 = (let _0_460 = (let _0_458 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check _0_458))
in (let _0_459 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _0_460 _0_459)))
in (FStar_Syntax_Util.abs _0_462 _0_461 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in ((mk_comp md) u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun uu____3389 celse -> (match (uu____3389) with
| (g, cthen) -> begin
(

let uu____3395 = (let _0_463 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _0_463 celse))
in (match (uu____3395) with
| ((md, uu____3409, uu____3410), (uu____3411, uu____3412, wp_then), (uu____3414, uu____3415, wp_else)) -> begin
(let _0_464 = (ifthenelse md res_t g wp_then wp_else)
in ((mk_comp md) u_res_t res_t _0_464 []))
end))
end)) lcases default_case)
in (

let uu____3426 = (let _0_465 = (FStar_Options.split_cases ())
in (_0_465 > (Prims.parse_int "0")))
in (match (uu____3426) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| uu____3427 -> begin
(

let comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____3430 = (destruct_comp comp)
in (match (uu____3430) with
| (uu____3434, uu____3435, wp) -> begin
(

let wp = ((let _0_470 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _0_469 = (let _0_468 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_467 = (let _0_466 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_466)::[])
in (_0_468)::_0_467))
in (FStar_Syntax_Syntax.mk_Tm_app _0_470 _0_469))) None wp.FStar_Syntax_Syntax.pos)
in ((mk_comp md) u_res_t res_t wp []))
end))))
end)))))
end))))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun uu____3460 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3464 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3464) with
| true -> begin
c
end
| uu____3467 -> begin
(

let uu____3468 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3468) with
| true -> begin
c
end
| uu____3471 -> begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _0_471 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_471)::[])
in (

let us = (let _0_473 = (let _0_472 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_0_472)::[])
in (u_res)::_0_473)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in ((let _0_480 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _0_479 = (let _0_478 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _0_477 = (let _0_476 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _0_475 = (let _0_474 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_474)::[])
in (_0_476)::_0_475))
in (_0_478)::_0_477))
in (FStar_Syntax_Syntax.mk_Tm_app _0_480 _0_479))) None wp0.FStar_Syntax_Syntax.pos))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3517 = (destruct_comp c)
in (match (uu____3517) with
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

let uu___128_3528 = lc
in {FStar_Syntax_Syntax.eff_name = uu___128_3528.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___128_3528.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___128_3528.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun uu____3543 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3547 = ((not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) || env.FStar_TypeChecker_Env.lax)
in (match (uu____3547) with
| true -> begin
c
end
| uu____3550 -> begin
(

let uu____3551 = (FStar_Syntax_Util.is_partial_return c)
in (match (uu____3551) with
| true -> begin
c
end
| uu____3554 -> begin
(

let uu____3555 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid))))
in (match (uu____3555) with
| true -> begin
(failwith (let _0_482 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _0_481 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _0_482 _0_481))))
end
| uu____3560 -> begin
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

let ret = (let _0_484 = (let _0_483 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _0_483 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_484))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _0_485 = ((bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret))).FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.comp_set_flags _0_485 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end))
end))
end))))
in (

let flags = (

let uu____3585 = (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc))))
in (match (uu____3585) with
| true -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____3587 -> begin
lc.FStar_Syntax_Syntax.cflags
end))
in (

let uu___129_3588 = lc
in {FStar_Syntax_Syntax.eff_name = uu___129_3588.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___129_3588.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____3607 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____3607) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_487 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (let _0_486 = (FStar_TypeChecker_Env.get_range env)
in ((_0_487), (_0_486)))))))
end
| Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let uu____3632 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3632) with
| FStar_Syntax_Syntax.Tm_type (uu____3635) -> begin
(

let uu____3636 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n
in (match (uu____3636) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let uu____3640 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc = (let _0_490 = (let _0_489 = (let _0_488 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_488))
in ((None), (_0_489)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _0_490))
in (

let e = ((let _0_492 = (let _0_491 = (FStar_Syntax_Syntax.as_arg e)
in (_0_491)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _0_492)) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((e), (lc))))))
end
| uu____3657 -> begin
((e), (lc))
end))
end
| uu____3658 -> begin
((e), (lc))
end)))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(let _0_493 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_0_493), (false)))
end
| uu____3685 -> begin
(let _0_494 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_0_494), (true)))
end)
in (match (gopt) with
| (None, uu____3690) -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___130_3693 = lc
in {FStar_Syntax_Syntax.eff_name = uu___130_3693.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___130_3693.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___130_3693.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard));
)
end
| (Some (g), apply_guard) -> begin
(

let uu____3697 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____3697) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let uu___131_3702 = lc
in {FStar_Syntax_Syntax.eff_name = uu___131_3702.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___131_3702.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___131_3702.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let uu___132_3705 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___132_3705.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___132_3705.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___132_3705.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____3711 -> (

let uu____3712 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3712) with
| true -> begin
(lc.FStar_Syntax_Syntax.comp ())
end
| uu____3715 -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let uu____3717 = (FStar_Syntax_Subst.compress f).FStar_Syntax_Syntax.n
in (match (uu____3717) with
| FStar_Syntax_Syntax.Tm_abs (uu____3720, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____3722; FStar_Syntax_Syntax.pos = uu____3723; FStar_Syntax_Syntax.vars = uu____3724}, uu____3725) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let uu___133_3749 = lc
in {FStar_Syntax_Syntax.eff_name = uu___133_3749.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___133_3749.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___133_3749.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| uu____3750 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in ((

let uu____3755 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3755) with
| true -> begin
(let _0_498 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _0_497 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _0_496 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _0_495 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _0_498 _0_497 _0_496 _0_495)))))
end
| uu____3756 -> begin
()
end));
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3758 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (uu____3758) with
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

let uu____3769 = (destruct_comp ct)
in (match (uu____3769) with
| (u_t, uu____3776, uu____3777) -> begin
(

let wp = ((let _0_503 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _0_502 = (let _0_501 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_500 = (let _0_499 = (FStar_Syntax_Syntax.as_arg xexp)
in (_0_499)::[])
in (_0_501)::_0_500))
in (FStar_Syntax_Syntax.mk_Tm_app _0_503 _0_502))) (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)
in (

let cret = (let _0_504 = ((mk_comp md) u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_504))
in (

let guard = (match (apply_guard) with
| true -> begin
((let _0_506 = (let _0_505 = (FStar_Syntax_Syntax.as_arg xexp)
in (_0_505)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _0_506)) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos)
end
| uu____3797 -> begin
f
end)
in (

let uu____3798 = (let _0_510 = (FStar_All.pipe_left (fun _0_507 -> Some (_0_507)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _0_509 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _0_508 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _0_510 _0_509 e cret _0_508))))
in (match (uu____3798) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let uu___134_3813 = x
in {FStar_Syntax_Syntax.ppname = uu___134_3813.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___134_3813.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _0_512 = (let _0_511 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_511))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _0_512 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in ((

let uu____3822 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3822) with
| true -> begin
(let _0_513 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _0_513))
end
| uu____3823 -> begin
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

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___93_3828 -> (match (uu___93_3828) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____3830 -> begin
[]
end))))
in (

let lc = (

let uu___135_3832 = lc
in (let _0_514 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _0_514; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let uu___136_3834 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___136_3834.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___136_3834.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___136_3834.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end))
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _0_517 = ((let _0_516 = (let _0_515 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name x))
in (_0_515)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _0_516)) None res_t.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.refine x _0_517))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____3864 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____3864) with
| true -> begin
((None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____3871 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (_)) | (FStar_Syntax_Syntax.Total (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____3888))::((ens, uu____3890))::uu____3891 -> begin
(let _0_520 = Some ((norm req))
in (let _0_519 = (let _0_518 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _0_518))
in ((_0_520), (_0_519))))
end
| uu____3914 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_522 = (let _0_521 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" _0_521))
in ((_0_522), (comp.FStar_Syntax_Syntax.pos))))))
end)
end
| uu____3923 -> begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____3929))::uu____3930 -> begin
(

let uu____3944 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (uu____3944) with
| (us_r, uu____3951) -> begin
(

let uu____3952 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (uu____3952) with
| (us_e, uu____3959) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _0_523 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_523 us_r))
in (

let as_ens = (let _0_524 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_524 us_e))
in (

let req = ((let _0_527 = (let _0_526 = (let _0_525 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_525)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_0_526)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _0_527)) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos)
in (

let ens = ((let _0_530 = (let _0_529 = (let _0_528 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_528)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_0_529)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _0_530)) None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos)
in (let _0_532 = Some ((norm req))
in (let _0_531 = (norm (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens))
in ((_0_532), (_0_531)))))))))
end))
end))
end
| uu____3994 -> begin
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
| uu____4019 -> begin
(

let number_of_implicits = (fun t -> (

let uu____4024 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____4024) with
| (formals, uu____4033) -> begin
(

let n_implicits = (

let uu____4045 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____4082 -> (match (uu____4082) with
| (uu____4086, imp) -> begin
((imp = None) || (imp = Some (FStar_Syntax_Syntax.Equality)))
end))))
in (match (uu____4045) with
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

let uu____4158 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____4158) with
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
(Prims.raise (FStar_Errors.Error ((let _0_537 = (let _0_535 = (FStar_Util.string_of_int n_expected)
in (let _0_534 = (FStar_Syntax_Print.term_to_string e)
in (let _0_533 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" _0_535 _0_534 _0_533))))
in (let _0_536 = (FStar_TypeChecker_Env.get_range env)
in ((_0_537), (_0_536)))))))
end
| uu____4179 -> begin
Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___94_4190 -> (match (uu___94_4190) with
| None -> begin
None
end
| Some (i) -> begin
Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4209 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4209) with
| (bs, c) -> begin
(

let rec aux = (fun subst inst_n bs -> (match (((inst_n), (bs))) with
| (Some (_0_538), uu____4270) when (_0_538 = (Prims.parse_int "0")) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____4292, ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let uu____4311 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (uu____4311) with
| (v, uu____4332, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let uu____4342 = (aux subst (decr_inst inst_n) rest)
in (match (uu____4342) with
| (args, bs, subst, g') -> begin
(let _0_539 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_0_539)))
end)))
end)))
end
| (uu____4404, bs) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____4428 = (let _0_540 = (inst_n_binders t)
in (aux [] _0_540 bs))
in (match (uu____4428) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], uu____4478) -> begin
((e), (torig), (guard))
end
| (uu____4494, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____4510 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____4529 -> begin
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
| uu____4544 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs = (fun univs -> (let _0_543 = (let _0_542 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _0_542 (FStar_List.map (fun u -> (let _0_541 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _0_541 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _0_543 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____4574 = (FStar_Util.set_is_empty x)
in (match (uu____4574) with
| true -> begin
[]
end
| uu____4576 -> begin
(

let s = (let _0_545 = (let _0_544 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _0_544))
in (FStar_All.pipe_right _0_545 FStar_Util.set_elements))
in ((

let uu____4582 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____4582) with
| true -> begin
(let _0_546 = (string_of_univs (FStar_TypeChecker_Env.univ_vars env))
in (FStar_Util.print1 "univ_vars in env: %s\n" _0_546))
end
| uu____4584 -> begin
()
end));
(

let r = Some ((FStar_TypeChecker_Env.get_range env))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____4598 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____4598) with
| true -> begin
(let _0_550 = (let _0_547 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _0_547))
in (let _0_549 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _0_548 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _0_550 _0_549 _0_548))))
end
| uu____4600 -> begin
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

let univnames = (let _0_551 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right _0_551 FStar_Util.fifo_set_elements))
in univnames))))


let maybe_set_tk = (fun ts uu___95_4641 -> (match (uu___95_4641) with
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
| ([], uu____4682) -> begin
generalized_univ_names
end
| (uu____4686, []) -> begin
explicit_univ_names
end
| uu____4690 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_553 = (let _0_552 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " _0_552))
in ((_0_553), (t.FStar_Syntax_Syntax.pos))))))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames = (gather_free_univnames env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in ((

let uu____4708 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____4708) with
| true -> begin
(let _0_554 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _0_554))
end
| uu____4710 -> begin
()
end));
(

let gen = (gen_univs env univs)
in ((

let uu____4714 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____4714) with
| true -> begin
(let _0_555 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _0_555))
end
| uu____4715 -> begin
()
end));
(

let univs = (check_universe_generalization univnames gen t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs t)
in (let _0_556 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs), (ts)) _0_556))));
));
)))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> (

let uu____4747 = (let _0_557 = (FStar_Util.for_all (fun uu____4752 -> (match (uu____4752) with
| (uu____4757, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _0_557))
in (match (uu____4747) with
| true -> begin
None
end
| uu____4774 -> begin
(

let norm = (fun c -> ((

let uu____4780 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____4780) with
| true -> begin
(let _0_558 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _0_558))
end
| uu____4781 -> begin
()
end));
(

let c = (

let uu____4783 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____4783) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
| uu____4784 -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end))
in ((

let uu____4786 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____4786) with
| true -> begin
(let _0_559 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _0_559))
end
| uu____4787 -> begin
()
end));
c;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _0_560 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _0_560 FStar_Util.set_elements)))
in (

let uu____4854 = (let _0_561 = (FStar_All.pipe_right ecs (FStar_List.map (fun uu____4943 -> (match (uu____4943) with
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
in (FStar_All.pipe_right _0_561 FStar_List.unzip))
in (match (uu____4854) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in ((

let uu____5072 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5072) with
| true -> begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end
| uu____5075 -> begin
()
end));
(

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun uu____5114 -> (match (uu____5114) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____5171 -> (match (uu____5171) with
| (u, k) -> begin
(

let uu____5191 = (FStar_Unionfind.find u)
in (match (uu____5191) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (uu____5229) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____5237 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let uu____5242 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____5242) with
| (bs, kres) -> begin
(

let a = (let _0_564 = (let _0_563 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_562 -> Some (_0_562)) _0_563))
in (FStar_Syntax_Syntax.new_bv _0_564 kres))
in (

let t = (let _0_566 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_565 = Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (FStar_Syntax_Syntax.mk_Total kres))))
in (FStar_Syntax_Util.abs bs _0_566 _0_565)))
in ((FStar_Syntax_Util.set_uvar u t);
((a), (Some (FStar_Syntax_Syntax.imp_tag)));
)))
end)))
end))
end))))
in (

let uu____5280 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], uu____5298) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e), (c))))
end
| uu____5310 -> begin
(

let uu____5318 = ((e), (c))
in (match (uu____5318) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (

let uu____5330 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c)).FStar_Syntax_Syntax.n
in (match (uu____5330) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____5345 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____5345) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| uu____5355 -> begin
(FStar_Syntax_Util.arrow tvars c)
end))
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _0_567 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_0_567)))))))
end))
end)
in (match (uu____5280) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs));
)))
end)))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> ((

let uu____5402 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5402) with
| true -> begin
(let _0_569 = (let _0_568 = (FStar_List.map (fun uu____5407 -> (match (uu____5407) with
| (lb, uu____5412, uu____5413) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _0_568 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _0_569))
end
| uu____5414 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____5422 -> (match (uu____5422) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____5437 = (let _0_570 = (FStar_All.pipe_right lecs (FStar_List.map (fun uu____5456 -> (match (uu____5456) with
| (uu____5462, e, c) -> begin
((e), (c))
end))))
in (gen env _0_570))
in (match (uu____5437) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____5494 -> (match (uu____5494) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun uu____5538 uu____5539 -> (match (((uu____5538), (uu____5539))) with
| ((l, uu____5572, uu____5573), (us, e, c)) -> begin
((

let uu____5599 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5599) with
| true -> begin
(let _0_574 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _0_573 = (FStar_Syntax_Print.lbname_to_string l)
in (let _0_572 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _0_571 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _0_574 _0_573 _0_572 _0_571)))))
end
| uu____5600 -> begin
()
end));
((l), (us), (e), (c));
)
end)) lecs ecs)
end))
in (FStar_List.map2 (fun univnames uu____5618 -> (match (uu____5618) with
| (l, generalized_univs, t, c) -> begin
(let _0_575 = (check_universe_generalization univnames generalized_univs t)
in ((l), (_0_575), (t), (c)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env t1 t2 -> (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end
| uu____5666 -> begin
(

let uu____5667 = (FStar_TypeChecker_Rel.try_subtype env t1 t2)
in (match (uu____5667) with
| None -> begin
None
end
| Some (f) -> begin
(let _0_577 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_576 -> Some (_0_576)) _0_577))
end))
end))
in (

let is_var = (fun e -> (

let uu____5676 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____5676) with
| FStar_Syntax_Syntax.Tm_name (uu____5677) -> begin
true
end
| uu____5678 -> begin
false
end)))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___137_5700 = x
in {FStar_Syntax_Syntax.ppname = uu___137_5700.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___137_5700.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| uu____5701 -> begin
(

let uu___138_5702 = e
in (let _0_578 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = uu___138_5702.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _0_578; FStar_Syntax_Syntax.pos = uu___138_5702.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___138_5702.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let uu___139_5709 = env
in (let _0_579 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___139_5709.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___139_5709.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___139_5709.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___139_5709.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___139_5709.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___139_5709.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___139_5709.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___139_5709.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___139_5709.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___139_5709.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___139_5709.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___139_5709.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___139_5709.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___139_5709.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___139_5709.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _0_579; FStar_TypeChecker_Env.is_iface = uu___139_5709.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___139_5709.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___139_5709.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___139_5709.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___139_5709.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___139_5709.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___139_5709.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___139_5709.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____5710 = (check env t1 t2)
in (match (uu____5710) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_581 = (FStar_TypeChecker_Err.expected_expression_of_type env t2 e t1)
in (let _0_580 = (FStar_TypeChecker_Env.get_range env)
in ((_0_581), (_0_580)))))))
end
| Some (g) -> begin
((

let uu____5718 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____5718) with
| true -> begin
(let _0_582 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _0_582))
end
| uu____5719 -> begin
()
end));
(let _0_583 = (decorate e t2)
in ((_0_583), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> ((FStar_TypeChecker_Rel.force_trivial_guard env g);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____5741 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____5741) with
| true -> begin
(let _0_585 = (discharge g)
in (let _0_584 = (lc.FStar_Syntax_Syntax.comp ())
in ((_0_585), (_0_584))))
end
| uu____5746 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _0_588 = (let _0_587 = (let _0_586 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _0_586 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _0_587 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _0_588 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let uu____5754 = (destruct_comp c)
in (match (uu____5754) with
| (u_t, t, wp) -> begin
(

let vc = (let _0_594 = (FStar_TypeChecker_Env.get_range env)
in ((let _0_593 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _0_592 = (let _0_591 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_590 = (let _0_589 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_589)::[])
in (_0_591)::_0_590))
in (FStar_Syntax_Syntax.mk_Tm_app _0_593 _0_592))) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _0_594))
in ((

let uu____5771 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____5771) with
| true -> begin
(let _0_595 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _0_595))
end
| uu____5772 -> begin
()
end));
(

let g = (let _0_596 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _0_596))
in (let _0_598 = (discharge g)
in (let _0_597 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_0_598), (_0_597)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f uu___96_5797 -> (match (uu___96_5797) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, uu____5803))::[] -> begin
(f fst)
end
| uu____5816 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _0_600 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _0_600 (fun _0_599 -> FStar_TypeChecker_Common.NonTrivial (_0_599)))))
in (

let op_or_e = (fun e -> (let _0_602 = (FStar_Syntax_Util.mk_neg (FStar_Syntax_Util.b2t e))
in (FStar_All.pipe_right _0_602 (fun _0_601 -> FStar_TypeChecker_Common.NonTrivial (_0_601)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_603 -> FStar_TypeChecker_Common.NonTrivial (_0_603))))
in (

let op_or_t = (fun t -> (let _0_605 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _0_605 (fun _0_604 -> FStar_TypeChecker_Common.NonTrivial (_0_604)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_606 -> FStar_TypeChecker_Common.NonTrivial (_0_606))))
in (

let short_op_ite = (fun uu___97_5848 -> (match (uu___97_5848) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____5854))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____5869))::[] -> begin
(let _0_608 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _0_608 (fun _0_607 -> FStar_TypeChecker_Common.NonTrivial (_0_607))))
end
| uu____5892 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (let _0_622 = (let _0_609 = (short_bin_op op_and_e)
in ((FStar_Syntax_Const.op_And), (_0_609)))
in (let _0_621 = (let _0_620 = (let _0_610 = (short_bin_op op_or_e)
in ((FStar_Syntax_Const.op_Or), (_0_610)))
in (let _0_619 = (let _0_618 = (let _0_611 = (short_bin_op op_and_t)
in ((FStar_Syntax_Const.and_lid), (_0_611)))
in (let _0_617 = (let _0_616 = (let _0_612 = (short_bin_op op_or_t)
in ((FStar_Syntax_Const.or_lid), (_0_612)))
in (let _0_615 = (let _0_614 = (let _0_613 = (short_bin_op op_imp_t)
in ((FStar_Syntax_Const.imp_lid), (_0_613)))
in (_0_614)::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[])
in (_0_616)::_0_615))
in (_0_618)::_0_617))
in (_0_620)::_0_619))
in (_0_622)::_0_621))
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____5945 = (FStar_Util.find_map table (fun uu____5951 -> (match (uu____5951) with
| (x, mk) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
Some ((mk seen_args))
end
| uu____5964 -> begin
None
end)
end)))
in (match (uu____5945) with
| None -> begin
FStar_TypeChecker_Common.Trivial
end
| Some (g) -> begin
g
end)))
end
| uu____5966 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____5970 = (FStar_Syntax_Util.un_uinst l).FStar_Syntax_Syntax.n
in (match (uu____5970) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| uu____5972 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, uu____5990))::uu____5991 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| uu____5997 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____6001, Some (FStar_Syntax_Syntax.Implicit (uu____6002))))::uu____6003 -> begin
bs
end
| uu____6012 -> begin
(

let uu____6013 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6013) with
| None -> begin
bs
end
| Some (t) -> begin
(

let uu____6016 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____6016) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____6018) -> begin
(

let uu____6029 = (FStar_Util.prefix_until (fun uu___98_6048 -> (match (uu___98_6048) with
| (uu____6052, Some (FStar_Syntax_Syntax.Implicit (uu____6053))) -> begin
false
end
| uu____6055 -> begin
true
end)) bs')
in (match (uu____6029) with
| None -> begin
bs
end
| Some ([], uu____6073, uu____6074) -> begin
bs
end
| Some (imps, uu____6111, uu____6112) -> begin
(

let uu____6149 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____6157 -> (match (uu____6157) with
| (x, uu____6162) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____6149) with
| true -> begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun uu____6185 -> (match (uu____6185) with
| (x, i) -> begin
(let _0_623 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_0_623), (i)))
end))))
in (FStar_List.append imps bs)))
end
| uu____6200 -> begin
bs
end))
end))
end
| uu____6201 -> begin
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
| uu____6219 -> begin
(let _0_624 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t)))))))) _0_624 e.FStar_Syntax_Syntax.pos))
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____6244 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid))
in (match (uu____6244) with
| true -> begin
e
end
| uu____6245 -> begin
(let _0_625 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t)))))))) _0_625 e.FStar_Syntax_Syntax.pos))
end))))


let effect_repr_aux = (fun only_reifiable env c u_c -> (

let uu____6286 = (let _0_626 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _0_626))
in (match (uu____6286) with
| None -> begin
None
end
| Some (ed) -> begin
(

let uu____6294 = (only_reifiable && (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))))
in (match (uu____6294) with
| true -> begin
None
end
| uu____6301 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
None
end
| uu____6307 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____6309 = (let _0_627 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_0_627)))
in (match (uu____6309) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in Some ((let _0_630 = (FStar_TypeChecker_Env.get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_629 = (let _0_628 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_0_628)::(wp)::[])
in ((repr), (_0_629)))))) None _0_630))))
end)))
end)
end))
end)))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (Prims.raise (FStar_Errors.Error ((let _0_632 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _0_631 = (FStar_TypeChecker_Env.get_range env)
in ((_0_632), (_0_631))))))))
in (

let uu____6394 = (let _0_633 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _0_633 u_c))
in (match (uu____6394) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____6422 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____6422) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(let _0_634 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _0_634));
)
end
| uu____6424 -> begin
()
end));
(

let fv = (let _0_635 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _0_635 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]), ([])))
in (let _0_636 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv))) None FStar_Range.dummyRange)
in ((sig_ctx), (_0_636)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___99_6456 -> (match (uu___99_6456) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____6457 -> begin
false
end))
in (

let reducibility = (fun uu___100_6461 -> (match (uu___100_6461) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____6462 -> begin
false
end))
in (

let assumption = (fun uu___101_6466 -> (match (uu___101_6466) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| uu____6467 -> begin
false
end))
in (

let reification = (fun uu___102_6471 -> (match (uu___102_6471) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| uu____6473 -> begin
false
end))
in (

let inferred = (fun uu___103_6477 -> (match (uu___103_6477) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| uu____6482 -> begin
false
end))
in (

let has_eq = (fun uu___104_6486 -> (match (uu___104_6486) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| uu____6487 -> begin
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
| uu____6512 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____6515 = (let _0_637 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___105_6517 -> (match (uu___105_6517) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____6518 -> begin
false
end))))
in (FStar_All.pipe_right _0_637 Prims.op_Negation))
in (match (uu____6515) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (Prims.raise (FStar_Errors.Error ((let _0_639 = (let _0_638 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" _0_638 msg))
in ((_0_639), (r)))))))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun uu____6535 -> (err' ""))
in ((match (((FStar_List.length quals) <> (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____6541 -> begin
()
end);
(

let uu____6543 = (not ((FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))))
in (match (uu____6543) with
| true -> begin
(err "ill-formed combination")
end
| uu____6545 -> begin
()
end));
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____6547), uu____6548, uu____6549, uu____6550, uu____6551) -> begin
((

let uu____6564 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____6564) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____6566 -> begin
()
end));
(

let uu____6567 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____6567) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____6570 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____6571) -> begin
(

let uu____6579 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))))
in (match (uu____6579) with
| true -> begin
(err' ())
end
| uu____6582 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____6583) -> begin
(

let uu____6590 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____6590) with
| true -> begin
(err' ())
end
| uu____6592 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____6593) -> begin
(

let uu____6599 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption)))))))
in (match (uu____6599) with
| true -> begin
(err' ())
end
| uu____6602 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____6603) -> begin
(

let uu____6606 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))))
in (match (uu____6606) with
| true -> begin
(err' ())
end
| uu____6609 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____6610) -> begin
(

let uu____6613 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))))
in (match (uu____6613) with
| true -> begin
(err' ())
end
| uu____6616 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____6617) -> begin
(

let uu____6627 = (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))))
in (match (uu____6627) with
| true -> begin
(err' ())
end
| uu____6630 -> begin
()
end))
end
| uu____6631 -> begin
()
end);
))))))
end
| uu____6632 -> begin
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

let inst_tc = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_640 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None))
in ((_0_640), (inst_univs)))))) None p)
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____6713 -> (match (uu____6713) with
| (x, imp) -> begin
(let _0_641 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_0_641), (imp)))
end))))
in ((FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p)))
in (

let unrefined_arg_binder = (FStar_Syntax_Syntax.mk_binder (projectee arg_typ))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____6726 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational None)
in (let _0_646 = (FStar_Syntax_Util.b2t ((let _0_645 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (let _0_644 = (let _0_643 = (let _0_642 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_642))
in (_0_643)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_645 _0_644))) None p))
in (FStar_Syntax_Util.refine x _0_646)))
in (FStar_Syntax_Syntax.mk_binder (

let uu___140_6739 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___140_6739.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_6739.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _0_647 = (FStar_List.map (fun uu____6757 -> (match (uu____6757) with
| (x, uu____6764) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append _0_647 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____6785 -> (match (uu____6785) with
| (x, uu____6792) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((fvq <> FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____6797 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((let _0_648 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_648)) || (FStar_Options.dont_gen_projectors (FStar_TypeChecker_Env.current_module env).FStar_Ident.str))
in (

let quals = (let _0_651 = (let _0_650 = (

let uu____6805 = (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit))
in (match (uu____6805) with
| true -> begin
(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____6807 -> begin
[]
end))
in (let _0_649 = (FStar_List.filter (fun uu___106_6808 -> (match (uu___106_6808) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____6809 -> begin
false
end)) iquals)
in (FStar_List.append _0_650 _0_649)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::[]
end
| uu____6804 -> begin
[]
end)) _0_651))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)))
in (let _0_652 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _0_652)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid discriminator_name))))
in ((

let uu____6823 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____6823) with
| true -> begin
(let _0_653 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" _0_653))
end
| uu____6824 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____6826 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Const.exp_true_bool
end
| uu____6828 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____6851 -> (match (uu____6851) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(let _0_655 = (pos (FStar_Syntax_Syntax.Pat_dot_term ((let _0_654 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_0_654), (FStar_Syntax_Syntax.tun))))))
in ((_0_655), (b)))
end
| uu____6869 -> begin
(let _0_656 = (pos (FStar_Syntax_Syntax.Pat_wild ((FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun))))
in ((_0_656), (b)))
end))
end))))
in (

let pat_true = (let _0_658 = (pos (FStar_Syntax_Syntax.Pat_cons ((let _0_657 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_0_657), (arg_pats))))))
in ((_0_658), (None), (FStar_Syntax_Const.exp_true_bool)))
in (

let pat_false = (let _0_659 = (pos (FStar_Syntax_Syntax.Pat_wild ((FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun))))
in ((_0_659), (None), (FStar_Syntax_Const.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst unrefined_arg_binder))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((let _0_663 = (let _0_662 = (FStar_Syntax_Util.branch pat_true)
in (let _0_661 = (let _0_660 = (FStar_Syntax_Util.branch pat_false)
in (_0_660)::[])
in (_0_662)::_0_661))
in ((arg_exp), (_0_663)))))) None p)))))
end)
in (

let dd = (

let uu____6920 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6920) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____6922 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____6930 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (let _0_665 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv discriminator_name dd None))
in (let _0_664 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _0_665; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _0_664}))
in (

let impl = FStar_Syntax_Syntax.Sig_let ((let _0_668 = (let _0_667 = (let _0_666 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _0_666 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_0_667)::[])
in ((((false), ((lb)::[]))), (p), (_0_668), (quals), ([]))))
in ((

let uu____6948 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____6948) with
| true -> begin
(let _0_669 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" _0_669))
end
| uu____6949 -> begin
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

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6968 -> (match (uu____6968) with
| (a, uu____6972) -> begin
(

let uu____6973 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____6973) with
| (field_name, uu____6977) -> begin
(

let field_proj_tm = (let _0_670 = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_670 inst_univs))
in (

let proj = ((FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[])) None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (let _0_691 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7003 -> (match (uu____7003) with
| (x, uu____7008) -> begin
(

let p = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____7010 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____7010) with
| (field_name, uu____7015) -> begin
(

let t = (let _0_672 = (let _0_671 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort))
in (FStar_Syntax_Util.arrow binders _0_671))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _0_672))
in (

let only_decl = (((let _0_673 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_673)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (FStar_Options.dont_gen_projectors (FStar_TypeChecker_Env.current_module env).FStar_Ident.str))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(let _0_674 = (FStar_List.filter (fun uu___107_7027 -> (match (uu___107_7027) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____7028 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_0_674)
end
| uu____7029 -> begin
q
end))
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___108_7036 -> (match (uu___108_7036) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____7037 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in ((

let uu____7041 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7041) with
| true -> begin
(let _0_675 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" _0_675))
end
| uu____7042 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____7044 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____7068 -> (match (uu____7068) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match (((i + ntps) = j)) with
| true -> begin
(let _0_676 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_0_676), (b)))
end
| uu____7086 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(let _0_678 = (pos (FStar_Syntax_Syntax.Pat_dot_term ((let _0_677 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_0_677), (FStar_Syntax_Syntax.tun))))))
in ((_0_678), (b)))
end
| uu____7095 -> begin
(let _0_679 = (pos (FStar_Syntax_Syntax.Pat_wild ((FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun))))
in ((_0_679), (b)))
end)
end))
end))))
in (

let pat = (let _0_682 = (pos (FStar_Syntax_Syntax.Pat_cons ((let _0_680 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_0_680), (arg_pats))))))
in (let _0_681 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_0_682), (None), (_0_681))))
in (

let body = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((let _0_684 = (let _0_683 = (FStar_Syntax_Util.branch pat)
in (_0_683)::[])
in ((arg_exp), (_0_684)))))) None p)
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let dd = (

let uu____7138 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____7138) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____7140 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____7142 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (let _0_686 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv field_name dd None))
in (let _0_685 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _0_686; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _0_685}))
in (

let impl = FStar_Syntax_Syntax.Sig_let ((let _0_689 = (let _0_688 = (let _0_687 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _0_687 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_0_688)::[])
in ((((false), ((lb)::[]))), (p), (_0_689), (quals), ([]))))
in ((

let uu____7160 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7160) with
| true -> begin
(let _0_690 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" _0_690))
end
| uu____7161 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____7163 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
)))))))
end)))
end))))
in (FStar_All.pipe_right _0_691 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, quals, uu____7188, r) when (not ((FStar_Ident.lid_equals constr_lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____7194 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____7194) with
| (univ_opening, uvs) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____7207 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____7207) with
| (formals, uu____7217) -> begin
(

let uu____7228 = (

let tps_opt = (FStar_Util.find_map tcs (fun se -> (

let uu____7241 = (let _0_692 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals typ_lid _0_692))
in (match (uu____7241) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7250, uvs', tps, typ0, uu____7254, constrs, uu____7256, uu____7257) -> begin
Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____7271 -> begin
(failwith "Impossible")
end)
end
| uu____7276 -> begin
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
| uu____7303 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____7228) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ0 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____7313 = (FStar_Syntax_Util.arrow_formals typ0)
in (match (uu____7313) with
| (indices, uu____7323) -> begin
(

let refine_domain = (

let uu____7335 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___109_7337 -> (match (uu___109_7337) with
| FStar_Syntax_Syntax.RecordConstructor (uu____7338) -> begin
true
end
| uu____7343 -> begin
false
end))))
in (match (uu____7335) with
| true -> begin
false
end
| uu____7344 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___110_7350 -> (match (uu___110_7350) with
| FStar_Syntax_Syntax.RecordConstructor (uu____7352, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____7359 -> begin
None
end))
in (

let uu____7360 = (FStar_Util.find_map quals filter_records)
in (match (uu____7360) with
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
| uu____7366 -> begin
iquals
end)
in (

let fields = (

let uu____7368 = (FStar_Util.first_N n_typars formals)
in (match (uu____7368) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____7399 uu____7400 -> (match (((uu____7399), (uu____7400))) with
| ((x, uu____7410), (x', uu____7412)) -> begin
FStar_Syntax_Syntax.NT ((let _0_693 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (_0_693))))
end)) imp_tps inductive_tps)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals fv_qual refine_domain env typ_lid constr_lid uvs inductive_tps indices fields)))))
end))))
end))
end)))
end))
end
| uu____7417 -> begin
[]
end))




