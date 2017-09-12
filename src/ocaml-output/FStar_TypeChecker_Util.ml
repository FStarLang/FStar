
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (

let uu____19 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____20 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.err uu____19 uu____20))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____25 = (

let uu____26 = (FStar_Syntax_Subst.compress t)
in uu____26.FStar_Syntax_Syntax.n)
in (match (uu____25) with
| FStar_Syntax_Syntax.Tm_type (uu____29) -> begin
true
end
| uu____30 -> begin
false
end)))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env -> (

let uu____41 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____41 (FStar_List.filter (fun uu____55 -> (match (uu____55) with
| (x, uu____61) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = (

let uu____75 = ((FStar_Options.full_context_dependency ()) || (

let uu____77 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____77)))
in (match (uu____75) with
| true -> begin
(FStar_TypeChecker_Env.all_binders env)
end
| uu____78 -> begin
(t_binders env)
end))
in (

let uu____79 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar uu____79 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (

let uu____88 = (new_uvar_aux env k)
in (FStar_Pervasives_Native.fst uu____88)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___102_98 -> (match (uu___102_98) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, uu____100); FStar_Syntax_Syntax.pos = uu____101; FStar_Syntax_Syntax.vars = uu____102} -> begin
uv
end
| uu____129 -> begin
(failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (

let uu____158 = (FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid)
in (match (uu____158) with
| FStar_Pervasives_Native.Some ((uu____181)::((tm, uu____183))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| uu____235 -> begin
(

let uu____246 = (new_uvar_aux env k)
in (match (uu____246) with
| (t, u) -> begin
(

let g = (

let uu___121_266 = FStar_TypeChecker_Rel.trivial_guard
in (

let uu____267 = (

let uu____282 = (

let uu____295 = (as_uvar u)
in ((reason), (env), (uu____295), (t), (k), (r)))
in (uu____282)::[])
in {FStar_TypeChecker_Env.guard_f = uu___121_266.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___121_266.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___121_266.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____267}))
in (

let uu____320 = (

let uu____327 = (

let uu____332 = (as_uvar u)
in ((uu____332), (r)))
in (uu____327)::[])
in ((t), (uu____320), (g))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____362 = (

let uu____363 = (FStar_Util.set_is_empty uvs)
in (not (uu____363)))
in (match (uu____362) with
| true -> begin
(

let us = (

let uu____369 = (

let uu____372 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun uu____390 -> (match (uu____390) with
| (x, uu____396) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) uu____372))
in (FStar_All.pipe_right uu____369 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____403 = (

let uu____404 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____404))
in (FStar_Errors.err r uu____403));
(FStar_Options.pop ());
))
end
| uu____405 -> begin
()
end))))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____419 -> (match (uu____419) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____429; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((match ((univ_vars1 <> [])) with
| true -> begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end
| uu____462 -> begin
()
end);
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder1 = (fun scope a -> (

let uu____475 = (

let uu____476 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in uu____476.FStar_Syntax_Syntax.n)
in (match (uu____475) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____483 = (FStar_Syntax_Util.type_u ())
in (match (uu____483) with
| (k, uu____493) -> begin
(

let t2 = (

let uu____495 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right uu____495 FStar_Pervasives_Native.fst))
in (((

let uu___122_505 = a
in {FStar_Syntax_Syntax.ppname = uu___122_505.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___122_505.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (false)))
end))
end
| uu____506 -> begin
((a), (true))
end)))
in (

let rec aux = (fun must_check_ty vars e1 -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e3, uu____543) -> begin
(aux must_check_ty vars e3)
end
| FStar_Syntax_Syntax.Tm_ascribed (e3, t2, uu____550) -> begin
(((FStar_Pervasives_Native.fst t2)), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____613) -> begin
(

let uu____634 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____694 uu____695 -> (match (((uu____694), (uu____695))) with
| ((scope, bs1, must_check_ty1), (a, imp)) -> begin
(

let uu____773 = (match (must_check_ty1) with
| true -> begin
((a), (true))
end
| uu____782 -> begin
(mk_binder1 scope a)
end)
in (match (uu____773) with
| (tb, must_check_ty2) -> begin
(

let b = ((tb), (imp))
in (

let bs2 = (FStar_List.append bs1 ((b)::[]))
in (

let scope1 = (FStar_List.append scope ((b)::[]))
in ((scope1), (bs2), (must_check_ty2)))))
end))
end)) ((vars), ([]), (must_check_ty))))
in (match (uu____634) with
| (scope, bs1, must_check_ty1) -> begin
(

let uu____885 = (aux must_check_ty1 scope body)
in (match (uu____885) with
| (res, must_check_ty2) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____914 = (FStar_Options.ml_ish ())
in (match (uu____914) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____915 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Util.arrow bs1 c)
in ((

let uu____921 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____921) with
| true -> begin
(

let uu____922 = (FStar_Range.string_of_range r)
in (

let uu____923 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____924 = (FStar_Util.string_of_bool must_check_ty2)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" uu____922 uu____923 uu____924))))
end
| uu____925 -> begin
()
end));
((FStar_Util.Inl (t2)), (must_check_ty2));
)))
end))
end))
end
| uu____934 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end
| uu____947 -> begin
(

let uu____948 = (

let uu____953 = (

let uu____954 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____954 FStar_Pervasives_Native.fst))
in FStar_Util.Inl (uu____953))
in ((uu____948), (false)))
end)
end)))
in (

let uu____967 = (

let uu____976 = (t_binders env)
in (aux false uu____976 e))
in (match (uu____967) with
| (t2, b) -> begin
(

let t3 = (match (t2) with
| FStar_Util.Inr (c) -> begin
(

let uu____1001 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____1001) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1004 -> begin
(

let uu____1005 = (

let uu____1006 = (

let uu____1011 = (

let uu____1012 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____1012))
in ((uu____1011), (rng)))
in FStar_Errors.Error (uu____1006))
in (FStar_Exn.raise uu____1005))
end))
end
| FStar_Util.Inl (t3) -> begin
t3
end)
in (([]), (t3), (b)))
end)))));
)
end
| uu____1020 -> begin
(

let uu____1021 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____1021) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let pat_as_exp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (([]), ([]), ([]), (env1), (e), (p1)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____1123) -> begin
(

let uu____1128 = (FStar_Syntax_Util.type_u ())
in (match (uu____1128) with
| (k, uu____1152) -> begin
(

let t = (new_uvar env1 k)
in (

let x1 = (

let uu___123_1155 = x
in {FStar_Syntax_Syntax.ppname = uu___123_1155.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_1155.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____1156 = (

let uu____1161 = (FStar_TypeChecker_Env.all_binders env1)
in (FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p uu____1161 t))
in (match (uu____1156) with
| (e, u) -> begin
(

let p2 = (

let uu___124_1185 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.p = uu___124_1185.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env1), (e), (p2)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____1195 = (FStar_Syntax_Util.type_u ())
in (match (uu____1195) with
| (t, uu____1219) -> begin
(

let x1 = (

let uu___125_1221 = x
in (

let uu____1222 = (new_uvar env1 t)
in {FStar_Syntax_Syntax.ppname = uu___125_1221.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___125_1221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1222}))
in (

let env2 = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env1 x1)
end
| uu____1226 -> begin
env1
end)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (p1)))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____1239 = (FStar_Syntax_Util.type_u ())
in (match (uu____1239) with
| (t, uu____1263) -> begin
(

let x1 = (

let uu___126_1265 = x
in (

let uu____1266 = (new_uvar env1 t)
in {FStar_Syntax_Syntax.ppname = uu___126_1265.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___126_1265.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1266}))
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x1)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ((x1)::[]), ([]), (env2), (e), (p1)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1299 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1426 uu____1427 -> (match (((uu____1426), (uu____1427))) with
| ((b, a, w, env2, args, pats1), (p2, imp)) -> begin
(

let uu____1616 = (pat_as_arg_with_env allow_wc_dependence env2 p2)
in (match (uu____1616) with
| (b', a', w', env3, te, pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1686 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), ((((pat), (imp)))::pats1)))
end))
end)) (([]), ([]), ([]), (env1), ([]), ([]))))
in (match (uu____1299) with
| (b, a, w, env2, args, pats1) -> begin
(

let e = (

let uu____1814 = (

let uu____1817 = (

let uu____1818 = (

let uu____1825 = (

let uu____1828 = (

let uu____1829 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____1830 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____1829 uu____1830)))
in (uu____1828 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in ((uu____1825), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____1818))
in (FStar_Syntax_Syntax.mk uu____1817))
in (uu____1814 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in (

let uu____1842 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____1853 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____1864 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____1842), (uu____1853), (uu____1864), (env2), (e), ((

let uu___127_1886 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___127_1886.FStar_Syntax_Syntax.p})))))))
end))
end))
in (

let rec elaborate_pat = (fun env1 p1 -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) r)
end
| uu____1924 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) r)
end))
in (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____1970 -> (match (uu____1970) with
| (p2, imp) -> begin
(

let uu____1989 = (elaborate_pat env1 p2)
in ((uu____1989), (imp)))
end)) pats)
in (

let uu____1994 = (FStar_TypeChecker_Env.lookup_datacon env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1994) with
| (uu____2001, t) -> begin
(

let uu____2003 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2003) with
| (f, uu____2019) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____2141)::uu____2142) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((uu____2193)::uu____2194, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____2272 -> (match (uu____2272) with
| (t1, imp) -> begin
(match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____2299 = (

let uu____2302 = (FStar_Syntax_Syntax.range_of_bv t1)
in FStar_Pervasives_Native.Some (uu____2302))
in (FStar_Syntax_Syntax.new_bv uu____2299 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2304 = (maybe_dot inaccessible a r)
in ((uu____2304), (true)))))
end
| uu____2309 -> begin
(

let uu____2312 = (

let uu____2313 = (

let uu____2318 = (

let uu____2319 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____2319))
in ((uu____2318), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Errors.Error (uu____2313))
in (FStar_Exn.raise uu____2312))
end)
end))))
end
| ((f1)::formals', ((p2, p_imp))::pats') -> begin
(match (f1) with
| (uu____2393, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____2394))) when p_imp -> begin
(

let uu____2397 = (aux formals' pats')
in (((p2), (true)))::uu____2397)
end
| (uu____2414, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p2.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p3 = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (

let uu____2422 = (aux formals' pats2)
in (((p3), (true)))::uu____2422)))
end
| (uu____2439, imp) -> begin
(

let uu____2445 = (

let uu____2452 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p2), (uu____2452)))
in (

let uu____2455 = (aux formals' pats')
in (uu____2445)::uu____2455))
end)
end))
in (

let uu___128_2470 = p1
in (

let uu____2473 = (

let uu____2474 = (

let uu____2487 = (aux f pats1)
in ((fv), (uu____2487)))
in FStar_Syntax_Syntax.Pat_cons (uu____2474))
in {FStar_Syntax_Syntax.v = uu____2473; FStar_Syntax_Syntax.p = uu___128_2470.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____2504 -> begin
p1
end)))
in (

let one_pat = (fun allow_wc_dependence env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____2538 = (pat_as_arg_with_env allow_wc_dependence env1 p2)
in (match (uu____2538) with
| (b, a, w, env2, arg, p3) -> begin
(

let uu____2591 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____2591) with
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2615 = (

let uu____2616 = (

let uu____2621 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in ((uu____2621), (p3.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____2616))
in (FStar_Exn.raise uu____2615))
end
| uu____2638 -> begin
((b), (a), (w), (arg), (p3))
end))
end))))
in (

let uu____2647 = (one_pat true env p)
in (match (uu____2647) with
| (b, uu____2673, uu____2674, tm, p1) -> begin
((b), (tm), (p1))
end))))))


let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.pat = (fun env p exp -> (

let qq = p
in (

let rec aux = (fun p1 e -> (

let pkg = (fun q -> (FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p))
in (

let e1 = (FStar_Syntax_Util.unmeta e)
in (match (((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n))) with
| (uu____2722, FStar_Syntax_Syntax.Tm_uinst (e2, uu____2724)) -> begin
(aux p1 e2)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____2729), FStar_Syntax_Syntax.Tm_constant (uu____2730)) -> begin
(pkg p1.FStar_Syntax_Syntax.v)
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____2734 = (

let uu____2735 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2736 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2735 uu____2736)))
in (failwith uu____2734))
end
| uu____2737 -> begin
()
end);
(

let uu____2739 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____2739) with
| true -> begin
(

let uu____2740 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2741 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____2740 uu____2741)))
end
| uu____2742 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___129_2745 = x
in {FStar_Syntax_Syntax.ppname = uu___129_2745.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_2745.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____2749 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____2749) with
| true -> begin
(

let uu____2750 = (

let uu____2751 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2752 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2751 uu____2752)))
in (failwith uu____2750))
end
| uu____2753 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___130_2756 = x
in {FStar_Syntax_Syntax.ppname = uu___130_2756.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___130_2756.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____2758), uu____2759) -> begin
(pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e1)))))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____2781 = (

let uu____2782 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____2782)))
in (match (uu____2781) with
| true -> begin
(

let uu____2783 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2783))
end
| uu____2784 -> begin
()
end));
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____2802; FStar_Syntax_Syntax.vars = uu____2803}, args)) -> begin
((

let uu____2842 = (

let uu____2843 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____2843 Prims.op_Negation))
in (match (uu____2842) with
| true -> begin
(

let uu____2844 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2844))
end
| uu____2845 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____2980))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3055)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3092) -> begin
(

let pat = (

let uu____3114 = (aux argpat e2)
in (

let uu____3115 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3114), (uu____3115))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3120 -> begin
(

let uu____3143 = (

let uu____3144 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3145 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3144 uu____3145)))
in (failwith uu____3143))
end))
in (match_args [] args argpats)));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____3157; FStar_Syntax_Syntax.vars = uu____3158}, uu____3159); FStar_Syntax_Syntax.pos = uu____3160; FStar_Syntax_Syntax.vars = uu____3161}, args)) -> begin
((

let uu____3204 = (

let uu____3205 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____3205 Prims.op_Negation))
in (match (uu____3204) with
| true -> begin
(

let uu____3206 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3206))
end
| uu____3207 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____3342))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3417)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3454) -> begin
(

let pat = (

let uu____3476 = (aux argpat e2)
in (

let uu____3477 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3476), (uu____3477))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3482 -> begin
(

let uu____3505 = (

let uu____3506 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3507 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3506 uu____3507)))
in (failwith uu____3505))
end))
in (match_args [] args argpats)));
)
end
| uu____3516 -> begin
(

let uu____3521 = (

let uu____3522 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____3523 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____3524 = (FStar_Syntax_Print.term_to_string exp)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____3522 uu____3523 uu____3524))))
in (failwith uu____3521))
end))))
in (aux p exp))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____3562 -> (match (uu____3562) with
| (p, i) -> begin
(

let uu____3579 = (decorated_pattern_as_term p)
in (match (uu____3579) with
| (vars, te) -> begin
(

let uu____3602 = (

let uu____3607 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____3607)))
in ((vars), (uu____3602)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____3621 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____3621)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____3625 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____3625)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____3629 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____3629)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3650 = (

let uu____3665 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____3665 FStar_List.unzip))
in (match (uu____3650) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____3775 = (

let uu____3776 = (

let uu____3777 = (

let uu____3792 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____3792), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____3777))
in (mk1 uu____3776))
in ((vars1), (uu____3775))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____3833))::[] -> begin
wp
end
| uu____3850 -> begin
(

let uu____3859 = (

let uu____3860 = (

let uu____3861 = (FStar_List.map (fun uu____3871 -> (match (uu____3871) with
| (x, uu____3877) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____3861 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____3860))
in (failwith uu____3859))
end)
in (

let uu____3882 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____3882), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____3899 = (destruct_comp c)
in (match (uu____3899) with
| (u, uu____3907, wp) -> begin
(

let uu____3909 = (

let uu____3918 = (

let uu____3919 = (lift.FStar_TypeChecker_Env.mlift_wp c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____3919))
in (uu____3918)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____3909; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____3932 = (

let uu____3939 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____3940 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____3939 uu____3940)))
in (match (uu____3932) with
| (m, uu____3942, uu____3943) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____3956 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____3956) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____3957 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____3996 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____3996) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____4033 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____4033) with
| (a, kwp) -> begin
(

let uu____4064 = (destruct_comp m1)
in (

let uu____4071 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____4064), (uu____4071))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (

let uu____4142 = (

let uu____4143 = (

let uu____4152 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4152)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____4143; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp uu____4142)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (match ((FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____4193 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu___131_4202 = lc
in (

let uu____4203 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___131_4202.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____4203; FStar_Syntax_Syntax.cflags = uu___131_4202.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____4208 -> (

let uu____4209 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst1 uu____4209)))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4214 = (

let uu____4215 = (FStar_Syntax_Subst.compress t)
in uu____4215.FStar_Syntax_Syntax.n)
in (match (uu____4214) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4218) -> begin
true
end
| uu____4231 -> begin
false
end)))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____4248 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4248) with
| true -> begin
c
end
| uu____4249 -> begin
(

let uu____4250 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4250) with
| true -> begin
c
end
| uu____4251 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____4289 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4289)::[])
in (

let us = (

let uu____4293 = (

let uu____4296 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____4296)::[])
in (u_res)::uu____4293)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____4300 = (

let uu____4301 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____4302 = (

let uu____4303 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4304 = (

let uu____4307 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____4308 = (

let uu____4311 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____4311)::[])
in (uu____4307)::uu____4308))
in (uu____4303)::uu____4304))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4301 uu____4302)))
in (uu____4300 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4315 = (destruct_comp c1)
in (match (uu____4315) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end)))


let close_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close1 = (fun uu____4346 -> (

let uu____4347 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp env bvs uu____4347)))
in (

let uu___132_4348 = lc
in {FStar_Syntax_Syntax.eff_name = uu___132_4348.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___132_4348.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___132_4348.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close1})))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v1 -> (

let c = (

let uu____4362 = (

let uu____4363 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____4363))
in (match (uu____4362) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____4364 -> begin
(

let m = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (

let uu____4368 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4368) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____4369 -> begin
(

let uu____4370 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____4370) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____4378 = (

let uu____4379 = (

let uu____4380 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____4381 = (

let uu____4382 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____4383 = (

let uu____4386 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____4386)::[])
in (uu____4382)::uu____4383))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4380 uu____4381)))
in (uu____4379 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env uu____4378)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
in ((

let uu____4390 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____4390) with
| true -> begin
(

let uu____4391 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____4392 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____4393 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4391 uu____4392 uu____4393))))
end
| uu____4394 -> begin
()
end));
c;
)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____4416 -> (match (uu____4416) with
| (b, lc2) -> begin
(

let lc11 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc21 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc11 lc21)
in ((

let uu____4429 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4429) with
| true -> begin
(

let bstr = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____4432 = (match (e1opt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (

let uu____4434 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____4435 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" uu____4432 uu____4434 bstr uu____4435)))))
end
| uu____4436 -> begin
()
end));
(

let bind_it = (fun uu____4440 -> (

let uu____4441 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4441) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____4443 -> begin
(

let c1 = (lc11.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc21.FStar_Syntax_Syntax.comp ())
in ((

let uu____4451 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4451) with
| true -> begin
(

let uu____4452 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____4454 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____4455 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____4456 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (

let uu____4457 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" uu____4452 uu____4454 uu____4455 uu____4456 uu____4457))))))
end
| uu____4458 -> begin
()
end));
(

let try_simplify = (fun uu____4472 -> (

let aux = (fun uu____4486 -> (

let uu____4487 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____4487) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____4516) -> begin
(

let uu____4517 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____4517) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____4536 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____4543 -> begin
(

let uu____4544 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____4544) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____4563 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____4600 = (

let uu____4605 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____4605), (reason)))
in FStar_Util.Inl (uu____4600))
end
| uu____4610 -> begin
(aux ())
end))
in (

let rec maybe_close = (fun t x c -> (

let uu____4629 = (

let uu____4630 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in uu____4630.FStar_Syntax_Syntax.n)
in (match (uu____4629) with
| FStar_Syntax_Syntax.Tm_refine (y, uu____4634) -> begin
(maybe_close y.FStar_Syntax_Syntax.sort x c)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____4640 -> begin
c
end)))
in (

let uu____4641 = (

let uu____4642 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____4642))
in (match (uu____4641) with
| true -> begin
(

let uu____4655 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____4655) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____4674 -> begin
(

let uu____4675 = (

let uu____4676 = (

let uu____4681 = (FStar_TypeChecker_Env.get_range env)
in (("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad"), (uu____4681)))
in FStar_Errors.Error (uu____4676))
in (FStar_Exn.raise uu____4675))
end))
end
| uu____4692 -> begin
(

let uu____4693 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____4693) with
| true -> begin
(subst_c2 "both total")
end
| uu____4704 -> begin
(

let uu____4705 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____4705) with
| true -> begin
(

let uu____4716 = (

let uu____4721 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____4721), ("both gtot")))
in FStar_Util.Inl (uu____4716))
end
| uu____4726 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____4747 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____4749 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____4749))))
in (match (uu____4747) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___133_4762 = x
in {FStar_Syntax_Syntax.ppname = uu___133_4762.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_4762.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____4763 = (

let uu____4768 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____4768), ("c1 Tot")))
in FStar_Util.Inl (uu____4763))))
end
| uu____4773 -> begin
(aux ())
end))
end
| uu____4774 -> begin
(aux ())
end)
end))
end))
end))))))
in (

let uu____4783 = (try_simplify ())
in (match (uu____4783) with
| FStar_Util.Inl (c, reason) -> begin
((

let uu____4807 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4807) with
| true -> begin
(

let uu____4808 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____4809 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____4810 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print4 "Simplified (because %s) bind %s %s to %s\n" reason uu____4808 uu____4809 uu____4810))))
end
| uu____4811 -> begin
()
end));
c;
)
end
| FStar_Util.Inr (reason) -> begin
(

let uu____4819 = (lift_and_destruct env c1 c2)
in (match (uu____4819) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4876 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____4876)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____4878 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4878)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____4891 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____4892 = (

let uu____4895 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____4896 = (

let uu____4899 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____4900 = (

let uu____4903 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____4904 = (

let uu____4907 = (

let uu____4908 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____4908))
in (uu____4907)::[])
in (uu____4903)::uu____4904))
in (uu____4899)::uu____4900))
in (uu____4895)::uu____4896))
in (uu____4891)::uu____4892))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (

let uu____4913 = (

let uu____4914 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____4914 wp_args))
in (uu____4913 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (mk_comp md u_t2 t2 wp [])))))))
end))
end)));
)))
end)))
in {FStar_Syntax_Syntax.eff_name = joined_eff; FStar_Syntax_Syntax.res_typ = lc21.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it});
))))
end))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (reason1) -> begin
(

let uu____4961 = (

let uu____4962 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____4962))
in (match (uu____4961) with
| true -> begin
f
end
| uu____4963 -> begin
(

let uu____4964 = (reason1 ())
in (label uu____4964 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___134_4978 = g
in (

let uu____4979 = (

let uu____4980 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____4980))
in {FStar_TypeChecker_Env.guard_f = uu____4979; FStar_TypeChecker_Env.deferred = uu___134_4978.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___134_4978.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___134_4978.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____4992 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____5014 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____5018 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5018) with
| true -> begin
c
end
| uu____5021 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____5025 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____5025) with
| true -> begin
c
end
| uu____5028 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____5030 = (destruct_comp c1)
in (match (uu____5030) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5046 = (

let uu____5047 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____5048 = (

let uu____5049 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5050 = (

let uu____5053 = (FStar_Syntax_Syntax.as_arg f1)
in (

let uu____5054 = (

let uu____5057 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5057)::[])
in (uu____5053)::uu____5054))
in (uu____5049)::uu____5050))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5047 uu____5048)))
in (uu____5046 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 c1.FStar_Syntax_Syntax.flags)))
end)))
end))
end)
end))))
in (

let uu___135_5060 = lc
in {FStar_Syntax_Syntax.eff_name = uu___135_5060.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___135_5060.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___135_5060.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> (

let uu____5098 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____5098) with
| true -> begin
((lc), (g0))
end
| uu____5103 -> begin
((

let uu____5105 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5105) with
| true -> begin
(

let uu____5106 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____5107 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" uu____5106 uu____5107)))
end
| uu____5108 -> begin
()
end));
(

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___103_5117 -> (match (uu___103_5117) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| uu____5120 -> begin
[]
end))))
in (

let strengthen = (fun uu____5126 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____5132 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____5134 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____5134) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c1 = (

let uu____5141 = ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (

let uu____5143 = (FStar_Syntax_Util.is_partial_return c)
in (not (uu____5143))))
in (match (uu____5141) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" FStar_Pervasives_Native.None (FStar_Syntax_Util.comp_result c))
in (

let xret = (

let uu____5150 = (

let uu____5151 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort uu____5151))
in (FStar_Syntax_Util.comp_set_flags uu____5150 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc1 = (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc1.FStar_Syntax_Syntax.comp ()))))
end
| uu____5155 -> begin
c
end))
in ((

let uu____5157 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5157) with
| true -> begin
(

let uu____5158 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____5159 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____5158 uu____5159)))
end
| uu____5160 -> begin
()
end));
(

let c2 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____5162 = (destruct_comp c2)
in (match (uu____5162) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5178 = (

let uu____5179 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____5180 = (

let uu____5181 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5182 = (

let uu____5185 = (

let uu____5186 = (

let uu____5187 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____5187 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5186))
in (

let uu____5188 = (

let uu____5191 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5191)::[])
in (uu____5185)::uu____5188))
in (uu____5181)::uu____5182))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5179 uu____5180)))
in (uu____5178 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in ((

let uu____5195 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5195) with
| true -> begin
(

let uu____5196 = (FStar_Syntax_Print.term_to_string wp1)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" uu____5196))
end
| uu____5197 -> begin
()
end));
(

let c21 = (mk_comp md u_res_t res_t wp1 flags)
in c21);
)))
end)));
))
end)))
end)))
in (

let uu____5199 = (

let uu___136_5200 = lc
in (

let uu____5201 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____5202 = (

let uu____5205 = ((FStar_Syntax_Util.is_pure_lcomp lc) && (

let uu____5207 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation uu____5207)))
in (match (uu____5205) with
| true -> begin
flags
end
| uu____5210 -> begin
[]
end))
in {FStar_Syntax_Syntax.eff_name = uu____5201; FStar_Syntax_Syntax.res_typ = uu___136_5200.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu____5202; FStar_Syntax_Syntax.comp = strengthen})))
in ((uu____5199), ((

let uu___137_5212 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___137_5212.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___137_5212.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___137_5212.FStar_TypeChecker_Env.implicits}))))));
)
end)))


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____5230 = (

let uu____5235 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____5236 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____5235), (uu____5236))))
in (match (uu____5230) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (

let uu____5245 = (

let uu____5246 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (

let uu____5247 = (

let uu____5248 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5249 = (

let uu____5252 = (FStar_Syntax_Syntax.as_arg yexp)
in (uu____5252)::[])
in (uu____5248)::uu____5249))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5246 uu____5247)))
in (uu____5245 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let x_eq_y_yret = (

let uu____5258 = (

let uu____5259 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (

let uu____5260 = (

let uu____5261 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5262 = (

let uu____5265 = (

let uu____5266 = (FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5266))
in (

let uu____5267 = (

let uu____5270 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (uu____5270)::[])
in (uu____5265)::uu____5267))
in (uu____5261)::uu____5262))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5259 uu____5260)))
in (uu____5258 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (

let uu____5276 = (

let uu____5277 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (

let uu____5278 = (

let uu____5279 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5280 = (

let uu____5283 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5284 = (

let uu____5287 = (

let uu____5288 = (

let uu____5289 = (

let uu____5290 = (FStar_Syntax_Syntax.mk_binder y)
in (uu____5290)::[])
in (FStar_Syntax_Util.abs uu____5289 x_eq_y_yret (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5288))
in (uu____5287)::[])
in (uu____5283)::uu____5284))
in (uu____5279)::uu____5280))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5277 uu____5278)))
in (uu____5276 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (

let uu____5297 = (FStar_TypeChecker_Env.get_range env)
in (bind uu____5297 env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp comp) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun uu____5320 -> (

let uu____5321 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5321) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end
| uu____5323 -> begin
(

let uu____5324 = (

let uu____5349 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (

let uu____5350 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____5349 uu____5350)))
in (match (uu____5324) with
| ((md, uu____5352, uu____5353), (u_res_t, res_t, wp_then), (uu____5357, uu____5358, wp_else)) -> begin
(

let ifthenelse = (fun md1 res_t1 g wp_t wp_e -> (

let uu____5396 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____5397 = (

let uu____5398 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md1 md1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____5399 = (

let uu____5400 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____5401 = (

let uu____5404 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____5405 = (

let uu____5408 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____5409 = (

let uu____5412 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____5412)::[])
in (uu____5408)::uu____5409))
in (uu____5404)::uu____5405))
in (uu____5400)::uu____5401))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5398 uu____5399)))
in (uu____5397 FStar_Pervasives_Native.None uu____5396))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let uu____5418 = (

let uu____5419 = (FStar_Options.split_cases ())
in (uu____5419 > (Prims.parse_int "0")))
in (match (uu____5418) with
| true -> begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end
| uu____5421 -> begin
(

let wp1 = (

let uu____5425 = (

let uu____5426 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____5427 = (

let uu____5428 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5429 = (

let uu____5432 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5432)::[])
in (uu____5428)::uu____5429))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5426 uu____5427)))
in (uu____5425 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end))
end)))
in (

let uu____5435 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____5435; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____5444 = (

let uu____5445 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____5445))
in (FStar_Syntax_Syntax.fvar uu____5444 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____5480 -> (match (uu____5480) with
| (uu____5485, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun uu____5490 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____5492 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5492) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____5493 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____5512 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____5513 = (

let uu____5514 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____5515 = (

let uu____5516 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____5517 = (

let uu____5520 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____5521 = (

let uu____5524 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____5525 = (

let uu____5528 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____5528)::[])
in (uu____5524)::uu____5525))
in (uu____5520)::uu____5521))
in (uu____5516)::uu____5517))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5514 uu____5515)))
in (uu____5513 FStar_Pervasives_Native.None uu____5512))))
in (

let default_case = (

let post_k = (

let uu____5535 = (

let uu____5542 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____5542)::[])
in (

let uu____5543 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5535 uu____5543)))
in (

let kwp = (

let uu____5549 = (

let uu____5556 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____5556)::[])
in (

let uu____5557 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5549 uu____5557)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____5562 = (

let uu____5563 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____5563)::[])
in (

let uu____5564 = (

let uu____5565 = (

let uu____5568 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____5568))
in (

let uu____5569 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____5565 uu____5569)))
in (FStar_Syntax_Util.abs uu____5562 uu____5564 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun uu____5593 celse -> (match (uu____5593) with
| (g, cthen) -> begin
(

let uu____5601 = (

let uu____5626 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____5626 celse))
in (match (uu____5601) with
| ((md, uu____5628, uu____5629), (uu____5630, uu____5631, wp_then), (uu____5633, uu____5634, wp_else)) -> begin
(

let uu____5654 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____5654 []))
end))
end)) lcases default_case)
in (

let uu____5655 = (

let uu____5656 = (FStar_Options.split_cases ())
in (uu____5656 > (Prims.parse_int "0")))
in (match (uu____5655) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| uu____5657 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____5660 = (destruct_comp comp1)
in (match (uu____5660) with
| (uu____5667, uu____5668, wp) -> begin
(

let wp1 = (

let uu____5673 = (

let uu____5674 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____5675 = (

let uu____5676 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5677 = (

let uu____5680 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5680)::[])
in (uu____5676)::uu____5677))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5674 uu____5675)))
in (uu____5673 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end)))))
end))))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let flags = (

let uu____5698 = (((

let uu____5701 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____5701))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (

let uu____5703 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____5703))))
in (match (uu____5698) with
| true -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____5706 -> begin
lc.FStar_Syntax_Syntax.cflags
end))
in (

let refine1 = (fun uu____5712 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____5716 = ((

let uu____5719 = (is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name)
in (not (uu____5719))) || env.FStar_TypeChecker_Env.lax)
in (match (uu____5716) with
| true -> begin
c
end
| uu____5722 -> begin
(

let uu____5723 = (FStar_Syntax_Util.is_partial_return c)
in (match (uu____5723) with
| true -> begin
c
end
| uu____5726 -> begin
(

let uu____5727 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____5727) with
| true -> begin
(

let uu____5730 = (

let uu____5731 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (not (uu____5731)))
in (match (uu____5730) with
| true -> begin
(

let uu____5734 = (

let uu____5735 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____5736 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" uu____5735 uu____5736)))
in (failwith uu____5734))
end
| uu____5739 -> begin
(

let retc = (return_value env (FStar_Syntax_Util.comp_result c) e)
in (

let uu____5741 = (

let uu____5742 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____5742)))
in (match (uu____5741) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___138_5747 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___138_5747.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___138_5747.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___138_5747.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____5748 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags)
end)))
end))
end
| uu____5749 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let t = c1.FStar_Syntax_Syntax.result_typ
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp c1)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let ret1 = (

let uu____5758 = (

let uu____5761 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____5761 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5758))
in (

let eq1 = (

let uu____5765 = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Util.mk_eq2 uu____5765 t xexp e))
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____5767 = (

let uu____5768 = (

let uu____5773 = (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp c2) ((FStar_Pervasives_Native.Some (x)), (eq_ret)))
in uu____5773.FStar_Syntax_Syntax.comp)
in (uu____5768 ()))
in (FStar_Syntax_Util.comp_set_flags uu____5767 flags))))))))))
end))
end))
end))))
in (

let uu___139_5776 = lc
in {FStar_Syntax_Syntax.eff_name = uu___139_5776.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___139_5776.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine1}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____5805 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____5805) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5814 = (

let uu____5815 = (

let uu____5820 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____5821 = (FStar_TypeChecker_Env.get_range env)
in ((uu____5820), (uu____5821))))
in FStar_Errors.Error (uu____5815))
in (FStar_Exn.raise uu____5814))
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____5858 = (

let uu____5859 = (FStar_Syntax_Subst.compress t2)
in uu____5859.FStar_Syntax_Syntax.n)
in (match (uu____5858) with
| FStar_Syntax_Syntax.Tm_type (uu____5862) -> begin
true
end
| uu____5863 -> begin
false
end))))
in (

let uu____5864 = (

let uu____5865 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in uu____5865.FStar_Syntax_Syntax.n)
in (match (uu____5864) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____5873 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let lc1 = (

let uu____5884 = (

let uu____5885 = (

let uu____5886 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5886))
in ((FStar_Pervasives_Native.None), (uu____5885)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____5884))
in (

let e1 = (

let uu____5896 = (

let uu____5897 = (

let uu____5898 = (FStar_Syntax_Syntax.as_arg e)
in (uu____5898)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5897))
in (uu____5896 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____5903 -> begin
((e), (lc))
end))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____5936 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____5936) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____5959 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____5981 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5981), (false)))
end
| uu____5986 -> begin
(

let uu____5987 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5987), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____5998) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____6007 = (

let uu____6008 = (

let uu____6013 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in ((uu____6013), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____6008))
in (FStar_Exn.raise uu____6007))
end
| uu____6020 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___140_6023 = lc
in {FStar_Syntax_Syntax.eff_name = uu___140_6023.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___140_6023.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___140_6023.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____6028 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____6028) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___141_6036 = lc
in {FStar_Syntax_Syntax.eff_name = uu___141_6036.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___141_6036.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___141_6036.FStar_Syntax_Syntax.comp})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___142_6039 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___142_6039.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___142_6039.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___142_6039.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____6045 -> (

let uu____6046 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____6046) with
| true -> begin
(lc.FStar_Syntax_Syntax.comp ())
end
| uu____6049 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in (

let uu____6051 = (

let uu____6052 = (FStar_Syntax_Subst.compress f1)
in uu____6052.FStar_Syntax_Syntax.n)
in (match (uu____6051) with
| FStar_Syntax_Syntax.Tm_abs (uu____6057, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6059; FStar_Syntax_Syntax.vars = uu____6060}, uu____6061) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___143_6083 = lc
in {FStar_Syntax_Syntax.eff_name = uu___143_6083.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___143_6083.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___143_6083.FStar_Syntax_Syntax.comp})
in (lc1.FStar_Syntax_Syntax.comp ()))
end
| uu____6084 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in ((

let uu____6089 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6089) with
| true -> begin
(

let uu____6090 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____6091 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____6092 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____6093 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____6090 uu____6091 uu____6092 uu____6093)))))
end
| uu____6094 -> begin
()
end));
(

let ct = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____6096 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____6096) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____6109 = (destruct_comp ct)
in (match (uu____6109) with
| (u_t, uu____6119, uu____6120) -> begin
(

let wp = (

let uu____6124 = (

let uu____6125 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (

let uu____6126 = (

let uu____6127 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6128 = (

let uu____6131 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____6131)::[])
in (uu____6127)::uu____6128))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6125 uu____6126)))
in (uu____6124 FStar_Pervasives_Native.None xexp.FStar_Syntax_Syntax.pos))
in (

let cret = (

let uu____6135 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6135))
in (

let guard = (match (apply_guard1) with
| true -> begin
(

let uu____6145 = (

let uu____6146 = (

let uu____6147 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____6147)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____6146))
in (uu____6145 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____6150 -> begin
f1
end)
in (

let uu____6151 = (

let uu____6156 = (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____6169 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____6170 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____6156 uu____6169 e cret uu____6170))))
in (match (uu____6151) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___144_6176 = x
in {FStar_Syntax_Syntax.ppname = uu___144_6176.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___144_6176.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____6178 = (

let uu____6179 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6179))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____6178 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (c1.FStar_Syntax_Syntax.comp ())
in ((

let uu____6190 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6190) with
| true -> begin
(

let uu____6191 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____6191))
end
| uu____6192 -> begin
()
end));
c2;
))))
end)))))
end))))))
end)));
))
end)))
end)))
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___104_6201 -> (match (uu___104_6201) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____6204 -> begin
[]
end))))
in (

let lc1 = (

let uu___145_6206 = lc
in (

let uu____6207 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____6207; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g2 = (

let uu___146_6209 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___146_6209.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___146_6209.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___146_6209.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____6234 = (

let uu____6235 = (

let uu____6236 = (

let uu____6237 = (

let uu____6238 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____6238))
in (uu____6237)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____6236))
in (uu____6235 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____6234))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____6245 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____6245) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____6256 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____6263) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____6278) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____6307))::((ens, uu____6309))::uu____6310 -> begin
(

let uu____6339 = (

let uu____6342 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____6342))
in (

let uu____6343 = (

let uu____6344 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____6344))
in ((uu____6339), (uu____6343))))
end
| uu____6347 -> begin
(

let uu____6356 = (

let uu____6357 = (

let uu____6362 = (

let uu____6363 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____6363))
in ((uu____6362), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____6357))
in (FStar_Exn.raise uu____6356))
end)
end
| uu____6370 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____6379))::uu____6380 -> begin
(

let uu____6399 = (

let uu____6404 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6404))
in (match (uu____6399) with
| (us_r, uu____6436) -> begin
(

let uu____6437 = (

let uu____6442 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6442))
in (match (uu____6437) with
| (us_e, uu____6474) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____6477 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6477 us_r))
in (

let as_ens = (

let uu____6479 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6479 us_e))
in (

let req = (

let uu____6483 = (

let uu____6484 = (

let uu____6485 = (

let uu____6496 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6496)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____6485)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____6484))
in (uu____6483 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____6514 = (

let uu____6515 = (

let uu____6516 = (

let uu____6527 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6527)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____6516)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____6515))
in (uu____6514 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____6542 = (

let uu____6545 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____6545))
in (

let uu____6546 = (

let uu____6547 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____6547))
in ((uu____6542), (uu____6546)))))))))
end))
end))
end
| uu____6550 -> begin
(failwith "Impossible")
end))
end)
end)
end)))))


let reify_body : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let tm = (FStar_Syntax_Util.mk_reify t)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____6578 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6578) with
| true -> begin
(

let uu____6579 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6580 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6579 uu____6580)))
end
| uu____6581 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____6601 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6601) with
| true -> begin
(

let uu____6602 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6603 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6602 uu____6603)))
end
| uu____6604 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____6609 = (

let uu____6610 = (

let uu____6611 = (FStar_Syntax_Subst.compress t)
in uu____6611.FStar_Syntax_Syntax.n)
in (match (uu____6610) with
| FStar_Syntax_Syntax.Tm_app (uu____6614) -> begin
false
end
| uu____6629 -> begin
true
end))
in (match (uu____6609) with
| true -> begin
t
end
| uu____6630 -> begin
(

let uu____6631 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6631) with
| (head1, args) -> begin
(

let uu____6668 = (

let uu____6669 = (

let uu____6670 = (FStar_Syntax_Subst.compress head1)
in uu____6670.FStar_Syntax_Syntax.n)
in (match (uu____6669) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____6673 -> begin
false
end))
in (match (uu____6668) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____6695 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____6704 -> begin
t
end))
end))
end)))


let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let torig = (FStar_Syntax_Subst.compress t)
in (match ((not (env.FStar_TypeChecker_Env.instantiate_imp))) with
| true -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____6730 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____6735 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____6735) with
| (formals, uu____6749) -> begin
(

let n_implicits = (

let uu____6767 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____6843 -> (match (uu____6843) with
| (uu____6850, imp) -> begin
((imp = FStar_Pervasives_Native.None) || (imp = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)))
end))))
in (match (uu____6767) with
| FStar_Pervasives_Native.None -> begin
(FStar_List.length formals)
end
| FStar_Pervasives_Native.Some (implicits, _first_explicit, _rest) -> begin
(FStar_List.length implicits)
end))
in n_implicits)
end)))
in (

let inst_n_binders = (fun t1 -> (

let uu____6981 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6981) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (expected_t) -> begin
(

let n_expected = (number_of_implicits expected_t)
in (

let n_available = (number_of_implicits t1)
in (match ((n_available < n_expected)) with
| true -> begin
(

let uu____7005 = (

let uu____7006 = (

let uu____7011 = (

let uu____7012 = (FStar_Util.string_of_int n_expected)
in (

let uu____7019 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7020 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____7012 uu____7019 uu____7020))))
in (

let uu____7027 = (FStar_TypeChecker_Env.get_range env)
in ((uu____7011), (uu____7027))))
in FStar_Errors.Error (uu____7006))
in (FStar_Exn.raise uu____7005))
end
| uu____7030 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___105_7048 -> (match (uu___105_7048) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7078 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7078) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_42), uu____7187) when (_0_42 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____7230, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____7263 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____7263) with
| (v1, uu____7303, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____7320 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____7320) with
| (args, bs3, subst3, g') -> begin
(

let uu____7413 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____7413)))
end)))
end)))
end
| (uu____7440, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____7486 = (

let uu____7513 = (inst_n_binders t)
in (aux [] uu____7513 bs1))
in (match (uu____7486) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____7584) -> begin
((e), (torig), (guard))
end
| (uu____7615, []) when (

let uu____7646 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____7646))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____7647 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____7679 -> begin
(FStar_Syntax_Util.arrow bs2 c1)
end)
in (

let t2 = (FStar_Syntax_Subst.subst subst1 t1)
in (

let e1 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in ((e1), (t2), (guard)))))
end)
end)))
end))
end
| uu____7694 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____7703 = (

let uu____7706 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____7706 (FStar_List.map (fun u -> (

let uu____7716 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____7716 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____7703 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____7735 = (FStar_Util.set_is_empty x)
in (match (uu____7735) with
| true -> begin
[]
end
| uu____7738 -> begin
(

let s = (

let uu____7742 = (

let uu____7745 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____7745))
in (FStar_All.pipe_right uu____7742 FStar_Util.set_elements))
in ((

let uu____7753 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7753) with
| true -> begin
(

let uu____7754 = (

let uu____7755 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____7755))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____7754))
end
| uu____7758 -> begin
()
end));
(

let r = (

let uu____7762 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____7762))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____7777 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7777) with
| true -> begin
(

let uu____7778 = (

let uu____7779 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7779))
in (

let uu____7780 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____7781 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____7778 uu____7780 uu____7781))))
end
| uu____7782 -> begin
()
end));
(FStar_Syntax_Unionfind.univ_change u (FStar_Syntax_Syntax.U_name (u_name)));
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

let univnames1 = (

let uu____7805 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____7805 FStar_Util.fifo_set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____7840) -> begin
generalized_univ_names
end
| (uu____7847, []) -> begin
explicit_univ_names
end
| uu____7854 -> begin
(

let uu____7863 = (

let uu____7864 = (

let uu____7869 = (

let uu____7870 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____7870))
in ((uu____7869), (t.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____7864))
in (FStar_Exn.raise uu____7863))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in (

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____7889 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7889) with
| true -> begin
(

let uu____7890 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____7890))
end
| uu____7891 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____7896 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7896) with
| true -> begin
(

let uu____7897 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" uu____7897))
end
| uu____7898 -> begin
()
end));
(

let univs2 = (check_universe_generalization univnames1 gen1 t0)
in (

let t1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env t)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs2 t1)
in ((univs2), (ts)))));
));
)))))


let gen : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list FStar_Pervasives_Native.option = (fun env is_rec lecs -> (

let uu____7962 = (

let uu____7963 = (FStar_Util.for_all (fun uu____7976 -> (match (uu____7976) with
| (uu____7985, uu____7986, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____7963))
in (match (uu____7962) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8018 -> begin
(

let norm1 = (fun c -> ((

let uu____8024 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8024) with
| true -> begin
(

let uu____8025 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____8025))
end
| uu____8026 -> begin
()
end));
(

let c1 = (

let uu____8028 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____8028) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
| uu____8029 -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end))
in ((

let uu____8031 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8031) with
| true -> begin
(

let uu____8032 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8032))
end
| uu____8033 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____8093 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____8093 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____8223 -> (match (uu____8223) with
| (lbname, e, c) -> begin
(

let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (

let c1 = (norm1 c)
in (

let t1 = (FStar_Syntax_Util.comp_result c1)
in (

let univs1 = (FStar_Syntax_Free.univs t1)
in (

let uvt = (FStar_Syntax_Free.uvars t1)
in ((

let uu____8289 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8289) with
| true -> begin
(

let uu____8290 = (

let uu____8291 = (

let uu____8294 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____8294 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8291 (FStar_String.concat ", ")))
in (

let uu____8321 = (

let uu____8322 = (

let uu____8325 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____8325 (FStar_List.map (fun uu____8353 -> (match (uu____8353) with
| (u, t2) -> begin
(

let uu____8360 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____8361 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s : %s)" uu____8360 uu____8361)))
end)))))
in (FStar_All.pipe_right uu____8322 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8290 uu____8321)))
end
| uu____8364 -> begin
()
end));
(

let univs2 = (

let uu____8368 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uu____8391 -> (match (uu____8391) with
| (uu____8400, t2) -> begin
(

let uu____8402 = (FStar_Syntax_Free.univs t2)
in (FStar_Util.set_union univs2 uu____8402))
end)) univs1 uu____8368))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____8425 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8425) with
| true -> begin
(

let uu____8426 = (

let uu____8427 = (

let uu____8430 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____8430 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8427 (FStar_String.concat ", ")))
in (

let uu____8457 = (

let uu____8458 = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____8490 -> (match (uu____8490) with
| (u, t2) -> begin
(

let uu____8497 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____8498 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s : %s)" uu____8497 uu____8498)))
end))))
in (FStar_All.pipe_right uu____8458 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8426 uu____8457)))
end
| uu____8501 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
))))))
end))
in (

let uu____8528 = (

let uu____8561 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____8561))
in (match (uu____8528) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____8675 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____8675) with
| true -> begin
()
end
| uu____8676 -> begin
(

let uu____8677 = lec_hd
in (match (uu____8677) with
| (lb1, uu____8685, uu____8686) -> begin
(

let uu____8687 = lec2
in (match (uu____8687) with
| (lb2, uu____8695, uu____8696) -> begin
(

let msg = (

let uu____8698 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8699 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____8698 uu____8699)))
in (

let uu____8700 = (

let uu____8701 = (

let uu____8706 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____8706)))
in FStar_Errors.Error (uu____8701))
in (FStar_Exn.raise uu____8700)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun uu____8817 -> (match (uu____8817) with
| (u, uu____8825) -> begin
(FStar_All.pipe_right u21 (FStar_Util.for_some (fun uu____8847 -> (match (uu____8847) with
| (u', uu____8855) -> begin
(FStar_Syntax_Unionfind.equiv u u')
end))))
end)))))
in (

let uu____8860 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____8860) with
| true -> begin
()
end
| uu____8861 -> begin
(

let uu____8862 = lec_hd
in (match (uu____8862) with
| (lb1, uu____8870, uu____8871) -> begin
(

let uu____8872 = lec2
in (match (uu____8872) with
| (lb2, uu____8880, uu____8881) -> begin
(

let msg = (

let uu____8883 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8884 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____8883 uu____8884)))
in (

let uu____8885 = (

let uu____8886 = (

let uu____8891 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____8891)))
in FStar_Errors.Error (uu____8886))
in (FStar_Exn.raise uu____8885)))
end))
end))
end))))
in (

let lecs1 = (

let uu____8901 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____8960 = (univs_and_uvars_of_lec this_lec)
in (match (uu____8960) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____8901 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (FStar_All.pipe_right uvs1 (FStar_List.map (fun uu____9138 -> (match (uu____9138) with
| (u, k) -> begin
(

let uu____9151 = (FStar_Syntax_Unionfind.find u)
in (match (uu____9151) with
| FStar_Pervasives_Native.Some (uu____9160) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____9167 -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env k)
in (

let uu____9171 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____9171) with
| (bs, kres) -> begin
(

let a = (

let uu____9209 = (

let uu____9212 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____9212))
in (FStar_Syntax_Syntax.new_bv uu____9209 kres))
in (

let t = (

let uu____9216 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____9216 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
in ((FStar_Syntax_Util.set_uvar u t);
((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)));
)))
end)))
end))
end)))))
in (

let gen_univs1 = (gen_univs env univs1)
in (

let gen_tvars = (gen_types uvs)
in (

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____9304 -> (match (uu____9304) with
| (lbname, e, c) -> begin
(

let uu____9340 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c))
end
| uu____9375 -> begin
(

let uu____9390 = ((e), (c))
in (match (uu____9390) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____9417 -> (match (uu____9417) with
| (x, uu____9425) -> begin
(

let uu____9430 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____9430))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____9440 = (

let uu____9441 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____9441))
in (match (uu____9440) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____9444 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____9445 -> begin
e1
end)
in (

let t = (

let uu____9449 = (

let uu____9450 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____9450.FStar_Syntax_Syntax.n)
in (match (uu____9449) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____9473 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____9473) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____9488 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____9490 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____9490))))))))
end))
end)
in (match (uu____9340) with
| (e1, c1) -> begin
((lbname), (gen_univs1), (e1), (c1))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env is_rec lecs -> ((

let uu____9578 = (Obj.magic (()))
in ());
(

let uu____9580 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____9580) with
| true -> begin
(

let uu____9581 = (

let uu____9582 = (FStar_List.map (fun uu____9595 -> (match (uu____9595) with
| (lb, uu____9603, uu____9604) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____9582 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____9581))
end
| uu____9607 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____9625 -> (match (uu____9625) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____9650 = (gen env is_rec lecs)
in (match (uu____9650) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____9729 -> (match (uu____9729) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____9777 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____9777) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____9813 -> (match (uu____9813) with
| (l, us, e, c) -> begin
(

let uu____9844 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____9845 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____9846 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____9847 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" uu____9844 uu____9845 uu____9846 uu____9847)))))
end))))
end
| uu____9848 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____9879 -> (match (uu____9879) with
| (l, generalized_univs, t, c) -> begin
(

let uu____9910 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____9910), (t), (c)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____9954 -> begin
(

let uu____9955 = (FStar_TypeChecker_Rel.try_subtype env2 t11 t21)
in (match (uu____9955) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____9961 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44)) uu____9961))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____9968 = (

let uu____9969 = (FStar_Syntax_Subst.compress e1)
in uu____9969.FStar_Syntax_Syntax.n)
in (match (uu____9968) with
| FStar_Syntax_Syntax.Tm_name (uu____9972) -> begin
true
end
| uu____9973 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___147_9989 = x
in {FStar_Syntax_Syntax.ppname = uu___147_9989.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___147_9989.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____9990 -> begin
e2
end)))
in (

let env2 = (

let uu___148_9992 = env1
in (

let uu____9993 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___148_9992.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___148_9992.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___148_9992.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___148_9992.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___148_9992.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___148_9992.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___148_9992.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___148_9992.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___148_9992.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___148_9992.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___148_9992.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___148_9992.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___148_9992.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___148_9992.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___148_9992.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____9993; FStar_TypeChecker_Env.is_iface = uu___148_9992.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___148_9992.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___148_9992.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___148_9992.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___148_9992.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___148_9992.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___148_9992.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___148_9992.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___148_9992.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___148_9992.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___148_9992.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___148_9992.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___148_9992.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___148_9992.FStar_TypeChecker_Env.identifier_info}))
in (

let uu____9994 = (check env2 t1 t2)
in (match (uu____9994) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10001 = (

let uu____10002 = (

let uu____10007 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____10008 = (FStar_TypeChecker_Env.get_range env2)
in ((uu____10007), (uu____10008))))
in FStar_Errors.Error (uu____10002))
in (FStar_Exn.raise uu____10001))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____10015 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____10015) with
| true -> begin
(

let uu____10016 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____10016))
end
| uu____10017 -> begin
()
end));
(

let uu____10018 = (decorate e t2)
in ((uu____10018), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____10049 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____10049) with
| true -> begin
(

let uu____10054 = (discharge g1)
in (

let uu____10055 = (lc.FStar_Syntax_Syntax.comp ())
in ((uu____10054), (uu____10055))))
end
| uu____10060 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c1 = (

let uu____10068 = (

let uu____10069 = (

let uu____10070 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____10070 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____10069 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____10068 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____10072 = (destruct_comp c1)
in (match (uu____10072) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____10089 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____10090 = (

let uu____10091 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____10092 = (

let uu____10093 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____10094 = (

let uu____10097 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____10097)::[])
in (uu____10093)::uu____10094))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10091 uu____10092)))
in (uu____10090 FStar_Pervasives_Native.None uu____10089)))
in ((

let uu____10101 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10101) with
| true -> begin
(

let uu____10102 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____10102))
end
| uu____10103 -> begin
()
end));
(

let g2 = (

let uu____10105 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____10105))
in (

let uu____10106 = (discharge g2)
in (

let uu____10107 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____10106), (uu____10107)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___106_10133 -> (match (uu___106_10133) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____10141))::[] -> begin
(f fst1)
end
| uu____10158 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____10163 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____10163 (fun _0_45 -> FStar_TypeChecker_Common.NonTrivial (_0_45)))))
in (

let op_or_e = (fun e -> (

let uu____10172 = (

let uu____10175 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____10175))
in (FStar_All.pipe_right uu____10172 (fun _0_46 -> FStar_TypeChecker_Common.NonTrivial (_0_46)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_47 -> FStar_TypeChecker_Common.NonTrivial (_0_47))))
in (

let op_or_t = (fun t -> (

let uu____10186 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____10186 (fun _0_48 -> FStar_TypeChecker_Common.NonTrivial (_0_48)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_49 -> FStar_TypeChecker_Common.NonTrivial (_0_49))))
in (

let short_op_ite = (fun uu___107_10200 -> (match (uu___107_10200) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____10208))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____10227))::[] -> begin
(

let uu____10256 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____10256 (fun _0_50 -> FStar_TypeChecker_Common.NonTrivial (_0_50))))
end
| uu____10261 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____10271 = (

let uu____10278 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____10278)))
in (

let uu____10283 = (

let uu____10292 = (

let uu____10299 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____10299)))
in (

let uu____10304 = (

let uu____10313 = (

let uu____10320 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____10320)))
in (

let uu____10325 = (

let uu____10334 = (

let uu____10341 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____10341)))
in (

let uu____10346 = (

let uu____10355 = (

let uu____10362 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____10362)))
in (uu____10355)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____10334)::uu____10346))
in (uu____10313)::uu____10325))
in (uu____10292)::uu____10304))
in (uu____10271)::uu____10283))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10413 = (FStar_Util.find_map table (fun uu____10426 -> (match (uu____10426) with
| (x, mk1) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
(

let uu____10443 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____10443))
end
| uu____10444 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (uu____10413) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____10446 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____10451 = (

let uu____10452 = (FStar_Syntax_Util.un_uinst l)
in uu____10452.FStar_Syntax_Syntax.n)
in (match (uu____10451) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____10456 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____10482))::uu____10483 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____10494 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____10501, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10502))))::uu____10503 -> begin
bs
end
| uu____10520 -> begin
(

let uu____10521 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____10521) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____10525 = (

let uu____10526 = (FStar_Syntax_Subst.compress t)
in uu____10526.FStar_Syntax_Syntax.n)
in (match (uu____10525) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____10530) -> begin
(

let uu____10547 = (FStar_Util.prefix_until (fun uu___108_10587 -> (match (uu___108_10587) with
| (uu____10594, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10595))) -> begin
false
end
| uu____10598 -> begin
true
end)) bs')
in (match (uu____10547) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____10633, uu____10634) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____10706, uu____10707) -> begin
(

let uu____10780 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____10798 -> (match (uu____10798) with
| (x, uu____10806) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____10780) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____10853 -> (match (uu____10853) with
| (x, i) -> begin
(

let uu____10872 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____10872), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____10881 -> begin
bs
end))
end))
end
| uu____10882 -> begin
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
| uu____10905 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____10923 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____10923) with
| true -> begin
e
end
| uu____10924 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____10950 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____10950) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(

let uu____10952 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) uu____10952));
)
end
| uu____10953 -> begin
()
end));
(

let fv = (

let uu____10955 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____10955 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____10963 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___149_10969 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___149_10969.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___149_10969.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___149_10969.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___149_10969.FStar_Syntax_Syntax.sigattrs})), (uu____10963)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___109_10981 -> (match (uu___109_10981) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____10982 -> begin
false
end))
in (

let reducibility = (fun uu___110_10986 -> (match (uu___110_10986) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| FStar_Syntax_Syntax.Visible_default -> begin
true
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
true
end
| uu____10987 -> begin
false
end))
in (

let assumption = (fun uu___111_10991 -> (match (uu___111_10991) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____10992 -> begin
false
end))
in (

let reification = (fun uu___112_10996 -> (match (uu___112_10996) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____10997) -> begin
true
end
| uu____10998 -> begin
false
end))
in (

let inferred = (fun uu___113_11002 -> (match (uu___113_11002) with
| FStar_Syntax_Syntax.Discriminator (uu____11003) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____11004) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____11009) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____11018) -> begin
true
end
| FStar_Syntax_Syntax.ExceptionConstructor -> begin
true
end
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____11027 -> begin
false
end))
in (

let has_eq = (fun uu___114_11031 -> (match (uu___114_11031) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____11032 -> begin
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
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (x = FStar_Syntax_Syntax.Abstract)) || (x = FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Visible_default -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (x = FStar_Syntax_Syntax.Abstract)) || (x = FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Irreducible -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (x = FStar_Syntax_Syntax.Abstract)) || (x = FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Abstract -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (x = FStar_Syntax_Syntax.Abstract)) || (x = FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Noeq -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (x = FStar_Syntax_Syntax.Abstract)) || (x = FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Unopteq -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (x = FStar_Syntax_Syntax.Abstract)) || (x = FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.TotalEffect -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((x = q) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Logic -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) || (inferred x)) || (visibility x)) || (reducibility x)))))
end
| FStar_Syntax_Syntax.Reifiable -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (x = FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Reflectable (uu____11092) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (x = FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11097 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____11101 = (

let uu____11102 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___115_11106 -> (match (uu___115_11106) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____11107 -> begin
false
end))))
in (FStar_All.pipe_right uu____11102 Prims.op_Negation))
in (match (uu____11101) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (

let uu____11120 = (

let uu____11121 = (

let uu____11126 = (

let uu____11127 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____11127 msg))
in ((uu____11126), (r)))
in FStar_Errors.Error (uu____11121))
in (FStar_Exn.raise uu____11120)))
in (

let err1 = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____11135 -> (err' ""))
in ((match (((FStar_List.length quals) <> (FStar_List.length no_dup_quals))) with
| true -> begin
(err1 "duplicate qualifiers")
end
| uu____11137 -> begin
()
end);
(

let uu____11139 = (

let uu____11140 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____11140)))
in (match (uu____11139) with
| true -> begin
(err1 "ill-formed combination")
end
| uu____11143 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____11145), uu____11146) -> begin
((

let uu____11162 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____11162) with
| true -> begin
(err1 "recursive definitions cannot be marked inline")
end
| uu____11165 -> begin
()
end));
(

let uu____11166 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____11166) with
| true -> begin
(err1 "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____11171 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____11172) -> begin
(

let uu____11181 = (

let uu____11182 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____11182)))
in (match (uu____11181) with
| true -> begin
(err'1 ())
end
| uu____11187 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____11188) -> begin
(

let uu____11195 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____11195) with
| true -> begin
(err'1 ())
end
| uu____11198 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____11199) -> begin
(

let uu____11206 = (

let uu____11207 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption)))))
in (not (uu____11207)))
in (match (uu____11206) with
| true -> begin
(err'1 ())
end
| uu____11212 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____11213) -> begin
(

let uu____11214 = (

let uu____11215 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11215)))
in (match (uu____11214) with
| true -> begin
(err'1 ())
end
| uu____11220 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____11221) -> begin
(

let uu____11222 = (

let uu____11223 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11223)))
in (match (uu____11222) with
| true -> begin
(err'1 ())
end
| uu____11228 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____11229) -> begin
(

let uu____11242 = (

let uu____11243 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____11243)))
in (match (uu____11242) with
| true -> begin
(err'1 ())
end
| uu____11248 -> begin
()
end))
end
| uu____11249 -> begin
()
end);
))))))
end
| uu____11250 -> begin
()
end)))))))))))


let mk_discriminator_and_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid uvs inductive_tps indices fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (FStar_Pervasives_Native.Some (p)) ptyp))
in (

let inst_univs = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) uvs)
in (

let tps = inductive_tps
in (

let arg_typ = (

let inst_tc = (

let uu____11322 = (

let uu____11325 = (

let uu____11326 = (

let uu____11333 = (

let uu____11334 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____11334))
in ((uu____11333), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____11326))
in (FStar_Syntax_Syntax.mk uu____11325))
in (uu____11322 FStar_Pervasives_Native.None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____11375 -> (match (uu____11375) with
| (x, imp) -> begin
(

let uu____11386 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____11386), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args FStar_Pervasives_Native.None p)))
in (

let unrefined_arg_binder = (

let uu____11388 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____11388))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____11390 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____11397 = (

let uu____11398 = (

let uu____11399 = (

let uu____11400 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____11401 = (

let uu____11402 = (

let uu____11403 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11403))
in (uu____11402)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____11400 uu____11401)))
in (uu____11399 FStar_Pervasives_Native.None p))
in (FStar_Syntax_Util.b2t uu____11398))
in (FStar_Syntax_Util.refine x uu____11397)))
in (

let uu____11406 = (

let uu___150_11407 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___150_11407.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_11407.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____11406)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____11422 = (FStar_List.map (fun uu____11444 -> (match (uu____11444) with
| (x, uu____11456) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____11422 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____11505 -> (match (uu____11505) with
| (x, uu____11517) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((fvq <> FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____11525 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((

let uu____11531 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____11531)) || (

let uu____11533 = (

let uu____11534 = (FStar_TypeChecker_Env.current_module env)
in uu____11534.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____11533)))
in (

let quals = (

let uu____11538 = (

let uu____11541 = (

let uu____11544 = (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit))
in (match (uu____11544) with
| true -> begin
(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____11547 -> begin
[]
end))
in (

let uu____11548 = (FStar_List.filter (fun uu___116_11552 -> (match (uu___116_11552) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11553 -> begin
false
end)) iquals)
in (FStar_List.append uu____11541 uu____11548)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::[]
end
| uu____11556 -> begin
[]
end)) uu____11538))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____11574 = (

let uu____11575 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____11575))
in (FStar_Syntax_Syntax.mk_Total uu____11574))
in (

let uu____11576 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____11576)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid discriminator_name); FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((

let uu____11579 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____11579) with
| true -> begin
(

let uu____11580 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____11580))
end
| uu____11581 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____11584 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____11590 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____11633 -> (match (uu____11633) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____11657 = (

let uu____11660 = (

let uu____11661 = (

let uu____11668 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____11668), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____11661))
in (pos uu____11660))
in ((uu____11657), (b)))
end
| uu____11671 -> begin
(

let uu____11672 = (

let uu____11675 = (

let uu____11676 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____11676))
in (pos uu____11675))
in ((uu____11672), (b)))
end))
end))))
in (

let pat_true = (

let uu____11694 = (

let uu____11697 = (

let uu____11698 = (

let uu____11711 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____11711), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____11698))
in (pos uu____11697))
in ((uu____11694), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_true_bool)))
in (

let pat_false = (

let uu____11745 = (

let uu____11748 = (

let uu____11749 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____11749))
in (pos uu____11748))
in ((uu____11745), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst unrefined_arg_binder))
in (

let uu____11761 = (

let uu____11764 = (

let uu____11765 = (

let uu____11788 = (

let uu____11791 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____11792 = (

let uu____11795 = (FStar_Syntax_Util.branch pat_false)
in (uu____11795)::[])
in (uu____11791)::uu____11792))
in ((arg_exp), (uu____11788)))
in FStar_Syntax_Syntax.Tm_match (uu____11765))
in (FStar_Syntax_Syntax.mk uu____11764))
in (uu____11761 FStar_Pervasives_Native.None p))))))
end)
in (

let dd = (

let uu____11802 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____11802) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____11805 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____11808 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____11810 = (

let uu____11815 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____11815))
in (

let uu____11816 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____11810; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____11816}))
in (

let impl = (

let uu____11820 = (

let uu____11821 = (

let uu____11828 = (

let uu____11831 = (

let uu____11832 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____11832 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____11831)::[])
in ((((false), ((lb)::[]))), (uu____11828)))
in FStar_Syntax_Syntax.Sig_let (uu____11821))
in {FStar_Syntax_Syntax.sigel = uu____11820; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____11850 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____11850) with
| true -> begin
(

let uu____11851 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____11851))
end
| uu____11852 -> begin
()
end));
(decl)::(impl)::[];
)))))))
end);
))))))))
end)
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst arg_binder))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____11893 -> (match (uu____11893) with
| (a, uu____11899) -> begin
(

let uu____11900 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____11900) with
| (field_name, uu____11906) -> begin
(

let field_proj_tm = (

let uu____11908 = (

let uu____11909 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____11909))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____11908 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) FStar_Pervasives_Native.None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____11926 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____11958 -> (match (uu____11958) with
| (x, uu____11966) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____11968 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____11968) with
| (field_name, uu____11976) -> begin
(

let t = (

let uu____11978 = (

let uu____11979 = (

let uu____11982 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____11982))
in (FStar_Syntax_Util.arrow binders uu____11979))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____11978))
in (

let only_decl = ((

let uu____11986 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____11986)) || (

let uu____11988 = (

let uu____11989 = (FStar_TypeChecker_Env.current_module env)
in uu____11989.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____11988)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____12003 = (FStar_List.filter (fun uu___117_12007 -> (match (uu___117_12007) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____12008 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____12003)
end
| uu____12009 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___118_12021 -> (match (uu___118_12021) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____12022 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let attrs = (match (only_decl) with
| true -> begin
[]
end
| uu____12034 -> begin
(FStar_Syntax_Util.attr_substitute)::[]
end)
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs}
in ((

let uu____12041 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12041) with
| true -> begin
(

let uu____12042 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____12042))
end
| uu____12043 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____12046 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____12090 -> (match (uu____12090) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match (((i + ntps) = j)) with
| true -> begin
(

let uu____12114 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____12114), (b)))
end
| uu____12119 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____12130 = (

let uu____12133 = (

let uu____12134 = (

let uu____12141 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____12141), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____12134))
in (pos uu____12133))
in ((uu____12130), (b)))
end
| uu____12144 -> begin
(

let uu____12145 = (

let uu____12148 = (

let uu____12149 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____12149))
in (pos uu____12148))
in ((uu____12145), (b)))
end)
end))
end))))
in (

let pat = (

let uu____12165 = (

let uu____12168 = (

let uu____12169 = (

let uu____12182 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____12182), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____12169))
in (pos uu____12168))
in (

let uu____12191 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____12165), (FStar_Pervasives_Native.None), (uu____12191))))
in (

let body = (

let uu____12203 = (

let uu____12206 = (

let uu____12207 = (

let uu____12230 = (

let uu____12233 = (FStar_Syntax_Util.branch pat)
in (uu____12233)::[])
in ((arg_exp), (uu____12230)))
in FStar_Syntax_Syntax.Tm_match (uu____12207))
in (FStar_Syntax_Syntax.mk uu____12206))
in (uu____12203 FStar_Pervasives_Native.None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let dd = (

let uu____12241 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____12241) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____12244 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____12246 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____12248 = (

let uu____12253 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____12253))
in (

let uu____12254 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____12248; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____12254}))
in (

let impl = (

let uu____12258 = (

let uu____12259 = (

let uu____12266 = (

let uu____12269 = (

let uu____12270 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____12270 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____12269)::[])
in ((((false), ((lb)::[]))), (uu____12266)))
in FStar_Syntax_Syntax.Sig_let (uu____12259))
in {FStar_Syntax_Syntax.sigel = uu____12258; FStar_Syntax_Syntax.sigrng = p1; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____12288 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12288) with
| true -> begin
(

let uu____12289 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____12289))
end
| uu____12290 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____12293 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
))))))))
end)))
end))))
in (FStar_All.pipe_right uu____11926 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, uu____12333) when (not ((FStar_Ident.lid_equals constr_lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____12338 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____12338) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____12360 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____12360) with
| (formals, uu____12376) -> begin
(

let uu____12393 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____12425 = (

let uu____12426 = (

let uu____12427 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____12427))
in (FStar_Ident.lid_equals typ_lid uu____12426))
in (match (uu____12425) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____12446, uvs', tps, typ0, uu____12450, constrs) -> begin
FStar_Pervasives_Native.Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____12469 -> begin
(failwith "Impossible")
end)
end
| uu____12478 -> begin
FStar_Pervasives_Native.None
end))))
in (match (tps_opt) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(match ((FStar_Ident.lid_equals typ_lid FStar_Parser_Const.exn_lid)) with
| true -> begin
(([]), (FStar_Syntax_Util.ktype0), (true))
end
| uu____12528 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____12393) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____12542 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____12542) with
| (indices, uu____12558) -> begin
(

let refine_domain = (

let uu____12576 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___119_12581 -> (match (uu___119_12581) with
| FStar_Syntax_Syntax.RecordConstructor (uu____12582) -> begin
true
end
| uu____12591 -> begin
false
end))))
in (match (uu____12576) with
| true -> begin
false
end
| uu____12592 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___120_12599 -> (match (uu___120_12599) with
| FStar_Syntax_Syntax.RecordConstructor (uu____12602, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____12614 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____12615 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____12615) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| FStar_Pervasives_Native.Some (q) -> begin
q
end)))
in (

let iquals1 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____12624 -> begin
iquals
end)
in (

let fields = (

let uu____12626 = (FStar_Util.first_N n_typars formals)
in (match (uu____12626) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____12691 uu____12692 -> (match (((uu____12691), (uu____12692))) with
| ((x, uu____12710), (x', uu____12712)) -> begin
(

let uu____12721 = (

let uu____12728 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____12728)))
in FStar_Syntax_Syntax.NT (uu____12721))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____12729 -> begin
[]
end))




