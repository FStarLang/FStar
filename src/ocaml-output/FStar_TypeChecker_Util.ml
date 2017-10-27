
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


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___128_98 -> (match (uu___128_98) with
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

let uu___147_266 = FStar_TypeChecker_Rel.trivial_guard
in (

let uu____267 = (

let uu____282 = (

let uu____295 = (as_uvar u)
in ((reason), (env), (uu____295), (t), (k), (r)))
in (uu____282)::[])
in {FStar_TypeChecker_Env.guard_f = uu___147_266.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___147_266.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___147_266.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____267}))
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
((match ((Prims.op_disEquality univ_vars1 [])) with
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

let uu___148_505 = a
in {FStar_Syntax_Syntax.ppname = uu___148_505.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_505.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (false)))
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


let pat_as_exp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p tc_annot -> (

let check_bv = (fun env1 x -> (

let t_x = (

let uu____1086 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in (match (uu____1086) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____1087; FStar_Syntax_Syntax.vars = uu____1088} -> begin
(

let uu____1091 = (FStar_Syntax_Util.type_u ())
in (match (uu____1091) with
| (t, uu____1097) -> begin
(new_uvar env1 t)
end))
end
| t -> begin
(tc_annot env1 t)
end))
in (

let uu___149_1099 = x
in {FStar_Syntax_Syntax.ppname = uu___149_1099.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___149_1099.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})))
in (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = (match (c) with
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(FStar_ToSyntax_ToSyntax.desugar_machine_integer env1.FStar_TypeChecker_Env.dsenv repr sw p1.FStar_Syntax_Syntax.p)
end
| uu____1164 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
end)
in (([]), ([]), ([]), (env1), (e), (p1)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____1172) -> begin
(

let uu____1177 = (FStar_Syntax_Util.type_u ())
in (match (uu____1177) with
| (k, uu____1201) -> begin
(

let t = (new_uvar env1 k)
in (

let x1 = (

let uu___150_1204 = x
in {FStar_Syntax_Syntax.ppname = uu___150_1204.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_1204.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____1205 = (

let uu____1210 = (FStar_TypeChecker_Env.all_binders env1)
in (FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p uu____1210 t))
in (match (uu____1205) with
| (e, u) -> begin
(

let p2 = (

let uu___151_1234 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.p = uu___151_1234.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env1), (e), (p2)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (check_bv env1 x)
in (

let env2 = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env1 x1)
end
| uu____1246 -> begin
env1
end)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (p1)))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (check_bv env1 x)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x1)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ((x1)::[]), ([]), (env2), (e), (p1)))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1290 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1417 uu____1418 -> (match (((uu____1417), (uu____1418))) with
| ((b, a, w, env2, args, pats1), (p2, imp)) -> begin
(

let uu____1607 = (pat_as_arg_with_env allow_wc_dependence env2 p2)
in (match (uu____1607) with
| (b', a', w', env3, te, pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1677 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), ((((pat), (imp)))::pats1)))
end))
end)) (([]), ([]), ([]), (env1), ([]), ([]))))
in (match (uu____1290) with
| (b, a, w, env2, args, pats1) -> begin
(

let e = (

let uu____1805 = (

let uu____1808 = (

let uu____1809 = (

let uu____1816 = (

let uu____1819 = (

let uu____1820 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____1821 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____1820 uu____1821)))
in (uu____1819 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in ((uu____1816), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____1809))
in (FStar_Syntax_Syntax.mk uu____1808))
in (uu____1805 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in (

let uu____1833 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____1844 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____1855 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____1833), (uu____1844), (uu____1855), (env2), (e), ((

let uu___152_1877 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___152_1877.FStar_Syntax_Syntax.p})))))))
end))
end))
in (

let rec elaborate_pat = (fun env1 p1 -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) r)
end
| uu____1915 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) r)
end))
in (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____1961 -> (match (uu____1961) with
| (p2, imp) -> begin
(

let uu____1980 = (elaborate_pat env1 p2)
in ((uu____1980), (imp)))
end)) pats)
in (

let uu____1985 = (FStar_TypeChecker_Env.lookup_datacon env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1985) with
| (uu____1992, t) -> begin
(

let uu____1994 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1994) with
| (f, uu____2010) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____2132)::uu____2133) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((uu____2184)::uu____2185, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____2263 -> (match (uu____2263) with
| (t1, imp) -> begin
(match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____2290 = (

let uu____2293 = (FStar_Syntax_Syntax.range_of_bv t1)
in FStar_Pervasives_Native.Some (uu____2293))
in (FStar_Syntax_Syntax.new_bv uu____2290 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2295 = (maybe_dot inaccessible a r)
in ((uu____2295), (true)))))
end
| uu____2300 -> begin
(

let uu____2303 = (

let uu____2304 = (

let uu____2309 = (

let uu____2310 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____2310))
in ((uu____2309), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Errors.Error (uu____2304))
in (FStar_Exn.raise uu____2303))
end)
end))))
end
| ((f1)::formals', ((p2, p_imp))::pats') -> begin
(match (f1) with
| (uu____2384, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____2385))) when p_imp -> begin
(

let uu____2388 = (aux formals' pats')
in (((p2), (true)))::uu____2388)
end
| (uu____2405, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p2.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p3 = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (

let uu____2413 = (aux formals' pats2)
in (((p3), (true)))::uu____2413)))
end
| (uu____2430, imp) -> begin
(

let uu____2436 = (

let uu____2443 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p2), (uu____2443)))
in (

let uu____2446 = (aux formals' pats')
in (uu____2436)::uu____2446))
end)
end))
in (

let uu___153_2461 = p1
in (

let uu____2464 = (

let uu____2465 = (

let uu____2478 = (aux f pats1)
in ((fv), (uu____2478)))
in FStar_Syntax_Syntax.Pat_cons (uu____2465))
in {FStar_Syntax_Syntax.v = uu____2464; FStar_Syntax_Syntax.p = uu___153_2461.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____2495 -> begin
p1
end)))
in (

let one_pat = (fun allow_wc_dependence env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____2529 = (pat_as_arg_with_env allow_wc_dependence env1 p2)
in (match (uu____2529) with
| (b, a, w, env2, arg, p3) -> begin
(

let uu____2582 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____2582) with
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2606 = (

let uu____2607 = (

let uu____2612 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in ((uu____2612), (p3.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____2607))
in (FStar_Exn.raise uu____2606))
end
| uu____2629 -> begin
((b), (a), (w), (arg), (p3))
end))
end))))
in (

let uu____2638 = (one_pat true env p)
in (match (uu____2638) with
| (b, uu____2664, uu____2665, tm, p1) -> begin
((b), (tm), (p1))
end)))))))


let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.pat = (fun env p exp -> (

let qq = p
in (

let rec aux = (fun p1 e -> (

let pkg = (fun q -> (FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p))
in (

let e1 = (FStar_Syntax_Util.unmeta e)
in (match (((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n))) with
| (uu____2713, FStar_Syntax_Syntax.Tm_uinst (e2, uu____2715)) -> begin
(aux p1 e2)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____2720), uu____2721) -> begin
(pkg p1.FStar_Syntax_Syntax.v)
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____2725 = (

let uu____2726 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2727 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2726 uu____2727)))
in (failwith uu____2725))
end
| uu____2728 -> begin
()
end);
(

let uu____2730 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____2730) with
| true -> begin
(

let uu____2731 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2732 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____2731 uu____2732)))
end
| uu____2733 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___154_2736 = x
in {FStar_Syntax_Syntax.ppname = uu___154_2736.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___154_2736.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____2740 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____2740) with
| true -> begin
(

let uu____2741 = (

let uu____2742 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2743 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2742 uu____2743)))
in (failwith uu____2741))
end
| uu____2744 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___155_2747 = x
in {FStar_Syntax_Syntax.ppname = uu___155_2747.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___155_2747.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____2749), uu____2750) -> begin
(pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e1)))))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____2772 = (

let uu____2773 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____2773)))
in (match (uu____2772) with
| true -> begin
(

let uu____2774 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2774))
end
| uu____2775 -> begin
()
end));
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____2793; FStar_Syntax_Syntax.vars = uu____2794}, args)) -> begin
((

let uu____2833 = (

let uu____2834 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____2834 Prims.op_Negation))
in (match (uu____2833) with
| true -> begin
(

let uu____2835 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2835))
end
| uu____2836 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____2971))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3046)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3083) -> begin
(

let pat = (

let uu____3105 = (aux argpat e2)
in (

let uu____3106 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3105), (uu____3106))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3111 -> begin
(

let uu____3134 = (

let uu____3135 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3136 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3135 uu____3136)))
in (failwith uu____3134))
end))
in (match_args [] args argpats)));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____3148; FStar_Syntax_Syntax.vars = uu____3149}, uu____3150); FStar_Syntax_Syntax.pos = uu____3151; FStar_Syntax_Syntax.vars = uu____3152}, args)) -> begin
((

let uu____3195 = (

let uu____3196 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____3196 Prims.op_Negation))
in (match (uu____3195) with
| true -> begin
(

let uu____3197 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3197))
end
| uu____3198 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____3333))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3408)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3445) -> begin
(

let pat = (

let uu____3467 = (aux argpat e2)
in (

let uu____3468 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3467), (uu____3468))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3473 -> begin
(

let uu____3496 = (

let uu____3497 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3498 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3497 uu____3498)))
in (failwith uu____3496))
end))
in (match_args [] args argpats)));
)
end
| uu____3507 -> begin
(

let uu____3512 = (

let uu____3513 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____3514 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____3515 = (FStar_Syntax_Print.term_to_string exp)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____3513 uu____3514 uu____3515))))
in (failwith uu____3512))
end))))
in (aux p exp))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____3553 -> (match (uu____3553) with
| (p, i) -> begin
(

let uu____3570 = (decorated_pattern_as_term p)
in (match (uu____3570) with
| (vars, te) -> begin
(

let uu____3593 = (

let uu____3598 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____3598)))
in ((vars), (uu____3593)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____3612 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____3612)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____3616 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____3616)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____3620 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____3620)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3641 = (

let uu____3656 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____3656 FStar_List.unzip))
in (match (uu____3641) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____3766 = (

let uu____3767 = (

let uu____3768 = (

let uu____3783 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____3783), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____3768))
in (mk1 uu____3767))
in ((vars1), (uu____3766))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____3824))::[] -> begin
wp
end
| uu____3841 -> begin
(

let uu____3850 = (

let uu____3851 = (

let uu____3852 = (FStar_List.map (fun uu____3862 -> (match (uu____3862) with
| (x, uu____3868) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____3852 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____3851))
in (failwith uu____3850))
end)
in (

let uu____3873 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____3873), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____3890 = (destruct_comp c)
in (match (uu____3890) with
| (u, uu____3898, wp) -> begin
(

let uu____3900 = (

let uu____3909 = (

let uu____3910 = (lift.FStar_TypeChecker_Env.mlift_wp c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____3910))
in (uu____3909)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____3900; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____3923 = (

let uu____3930 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____3931 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____3930 uu____3931)))
in (match (uu____3923) with
| (m, uu____3933, uu____3934) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____3947 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____3947) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____3948 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____3987 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____3987) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____4024 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____4024) with
| (a, kwp) -> begin
(

let uu____4055 = (destruct_comp m1)
in (

let uu____4062 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____4055), (uu____4062))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (

let uu____4133 = (

let uu____4134 = (

let uu____4143 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4143)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____4134; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp uu____4133)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (match ((FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____4184 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu___156_4193 = lc
in (

let uu____4194 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___156_4193.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____4194; FStar_Syntax_Syntax.cflags = uu___156_4193.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____4199 -> (

let uu____4200 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst1 uu____4200)))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4205 = (

let uu____4206 = (FStar_Syntax_Subst.compress t)
in uu____4206.FStar_Syntax_Syntax.n)
in (match (uu____4205) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4209) -> begin
true
end
| uu____4222 -> begin
false
end)))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____4239 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4239) with
| true -> begin
c
end
| uu____4240 -> begin
(

let uu____4241 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4241) with
| true -> begin
c
end
| uu____4242 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____4280 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4280)::[])
in (

let us = (

let uu____4284 = (

let uu____4287 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____4287)::[])
in (u_res)::uu____4284)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____4291 = (

let uu____4292 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____4293 = (

let uu____4294 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4295 = (

let uu____4298 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____4299 = (

let uu____4302 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____4302)::[])
in (uu____4298)::uu____4299))
in (uu____4294)::uu____4295))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4292 uu____4293)))
in (uu____4291 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4306 = (destruct_comp c1)
in (match (uu____4306) with
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

let close1 = (fun uu____4337 -> (

let uu____4338 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp env bvs uu____4338)))
in (

let uu___157_4339 = lc
in {FStar_Syntax_Syntax.eff_name = uu___157_4339.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___157_4339.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___157_4339.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close1})))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v1 -> (

let c = (

let uu____4353 = (

let uu____4354 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____4354))
in (match (uu____4353) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____4355 -> begin
(

let uu____4356 = (FStar_Syntax_Util.is_unit t)
in (match (uu____4356) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero)))
end
| uu____4357 -> begin
(

let m = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (

let uu____4361 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4361) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____4362 -> begin
(

let uu____4363 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____4363) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____4371 = (

let uu____4372 = (

let uu____4373 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____4374 = (

let uu____4375 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____4376 = (

let uu____4379 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____4379)::[])
in (uu____4375)::uu____4376))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4373 uu____4374)))
in (uu____4372 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env uu____4371)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
end))
in ((

let uu____4383 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____4383) with
| true -> begin
(

let uu____4384 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____4385 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____4386 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4384 uu____4385 uu____4386))))
end
| uu____4387 -> begin
()
end));
c;
)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____4409 -> (match (uu____4409) with
| (b, lc2) -> begin
(

let lc11 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc21 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc11 lc21)
in ((

let uu____4422 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4422) with
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

let uu____4425 = (match (e1opt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (

let uu____4427 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____4428 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" uu____4425 uu____4427 bstr uu____4428)))))
end
| uu____4429 -> begin
()
end));
(

let bind_it = (fun uu____4433 -> (

let uu____4434 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4434) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____4436 -> begin
(

let c1 = (lc11.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc21.FStar_Syntax_Syntax.comp ())
in ((

let uu____4444 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4444) with
| true -> begin
(

let uu____4445 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____4447 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____4448 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____4449 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (

let uu____4450 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" uu____4445 uu____4447 uu____4448 uu____4449 uu____4450))))))
end
| uu____4451 -> begin
()
end));
(

let try_simplify = (fun uu____4465 -> (

let aux = (fun uu____4479 -> (

let uu____4480 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____4480) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____4509) -> begin
(

let uu____4510 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____4510) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____4529 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____4536 -> begin
(

let uu____4537 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____4537) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____4556 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____4593 = (

let uu____4598 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____4598), (reason)))
in FStar_Util.Inl (uu____4593))
end
| uu____4603 -> begin
(aux ())
end))
in (

let rec maybe_close = (fun t x c -> (

let uu____4622 = (

let uu____4623 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in uu____4623.FStar_Syntax_Syntax.n)
in (match (uu____4622) with
| FStar_Syntax_Syntax.Tm_refine (y, uu____4627) -> begin
(maybe_close y.FStar_Syntax_Syntax.sort x c)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____4633 -> begin
c
end)))
in (

let uu____4634 = (

let uu____4635 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____4635))
in (match (uu____4634) with
| true -> begin
(

let uu____4648 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____4648) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____4667 -> begin
(

let uu____4668 = (

let uu____4669 = (

let uu____4674 = (FStar_TypeChecker_Env.get_range env)
in (("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad"), (uu____4674)))
in FStar_Errors.Error (uu____4669))
in (FStar_Exn.raise uu____4668))
end))
end
| uu____4685 -> begin
(

let uu____4686 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____4686) with
| true -> begin
(subst_c2 "both total")
end
| uu____4697 -> begin
(

let uu____4698 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____4698) with
| true -> begin
(

let uu____4709 = (

let uu____4714 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____4714), ("both gtot")))
in FStar_Util.Inl (uu____4709))
end
| uu____4719 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____4740 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____4742 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____4742))))
in (match (uu____4740) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___158_4755 = x
in {FStar_Syntax_Syntax.ppname = uu___158_4755.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_4755.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____4756 = (

let uu____4761 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____4761), ("c1 Tot")))
in FStar_Util.Inl (uu____4756))))
end
| uu____4766 -> begin
(aux ())
end))
end
| uu____4767 -> begin
(aux ())
end)
end))
end))
end))))))
in (

let uu____4776 = (try_simplify ())
in (match (uu____4776) with
| FStar_Util.Inl (c, reason) -> begin
((

let uu____4800 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4800) with
| true -> begin
(

let uu____4801 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____4802 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____4803 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print4 "Simplified (because %s) bind %s %s to %s\n" reason uu____4801 uu____4802 uu____4803))))
end
| uu____4804 -> begin
()
end));
c;
)
end
| FStar_Util.Inr (reason) -> begin
(

let uu____4812 = (lift_and_destruct env c1 c2)
in (match (uu____4812) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4869 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____4869)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____4871 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4871)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____4884 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____4885 = (

let uu____4888 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____4889 = (

let uu____4892 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____4893 = (

let uu____4896 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____4897 = (

let uu____4900 = (

let uu____4901 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____4901))
in (uu____4900)::[])
in (uu____4896)::uu____4897))
in (uu____4892)::uu____4893))
in (uu____4888)::uu____4889))
in (uu____4884)::uu____4885))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (

let uu____4906 = (

let uu____4907 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____4907 wp_args))
in (uu____4906 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
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

let uu____4954 = (

let uu____4955 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____4955))
in (match (uu____4954) with
| true -> begin
f
end
| uu____4956 -> begin
(

let uu____4957 = (reason1 ())
in (label uu____4957 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___159_4971 = g
in (

let uu____4972 = (

let uu____4973 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____4973))
in {FStar_TypeChecker_Env.guard_f = uu____4972; FStar_TypeChecker_Env.deferred = uu___159_4971.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___159_4971.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___159_4971.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____4985 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____5007 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____5011 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5011) with
| true -> begin
c
end
| uu____5014 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____5018 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____5018) with
| true -> begin
c
end
| uu____5021 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____5023 = (destruct_comp c1)
in (match (uu____5023) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5039 = (

let uu____5040 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____5041 = (

let uu____5042 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5043 = (

let uu____5046 = (FStar_Syntax_Syntax.as_arg f1)
in (

let uu____5047 = (

let uu____5050 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5050)::[])
in (uu____5046)::uu____5047))
in (uu____5042)::uu____5043))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5040 uu____5041)))
in (uu____5039 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 c1.FStar_Syntax_Syntax.flags)))
end)))
end))
end)
end))))
in (

let uu___160_5053 = lc
in {FStar_Syntax_Syntax.eff_name = uu___160_5053.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___160_5053.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___160_5053.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> (

let uu____5091 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____5091) with
| true -> begin
((lc), (g0))
end
| uu____5096 -> begin
((

let uu____5098 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5098) with
| true -> begin
(

let uu____5099 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____5100 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" uu____5099 uu____5100)))
end
| uu____5101 -> begin
()
end));
(

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___129_5110 -> (match (uu___129_5110) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| uu____5113 -> begin
[]
end))))
in (

let strengthen = (fun uu____5119 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____5125 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____5127 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____5127) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c1 = (

let uu____5134 = ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (

let uu____5136 = (FStar_Syntax_Util.is_partial_return c)
in (not (uu____5136))))
in (match (uu____5134) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" FStar_Pervasives_Native.None (FStar_Syntax_Util.comp_result c))
in (

let xret = (

let uu____5143 = (

let uu____5144 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort uu____5144))
in (FStar_Syntax_Util.comp_set_flags uu____5143 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc1 = (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc1.FStar_Syntax_Syntax.comp ()))))
end
| uu____5148 -> begin
c
end))
in ((

let uu____5150 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5150) with
| true -> begin
(

let uu____5151 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____5152 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____5151 uu____5152)))
end
| uu____5153 -> begin
()
end));
(

let c2 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____5155 = (destruct_comp c2)
in (match (uu____5155) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5171 = (

let uu____5172 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____5173 = (

let uu____5174 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5175 = (

let uu____5178 = (

let uu____5179 = (

let uu____5180 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____5180 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5179))
in (

let uu____5181 = (

let uu____5184 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5184)::[])
in (uu____5178)::uu____5181))
in (uu____5174)::uu____5175))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5172 uu____5173)))
in (uu____5171 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in ((

let uu____5188 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5188) with
| true -> begin
(

let uu____5189 = (FStar_Syntax_Print.term_to_string wp1)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" uu____5189))
end
| uu____5190 -> begin
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

let uu____5192 = (

let uu___161_5193 = lc
in (

let uu____5194 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____5195 = (

let uu____5198 = ((FStar_Syntax_Util.is_pure_lcomp lc) && (

let uu____5200 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation uu____5200)))
in (match (uu____5198) with
| true -> begin
flags
end
| uu____5203 -> begin
[]
end))
in {FStar_Syntax_Syntax.eff_name = uu____5194; FStar_Syntax_Syntax.res_typ = uu___161_5193.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu____5195; FStar_Syntax_Syntax.comp = strengthen})))
in ((uu____5192), ((

let uu___162_5205 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___162_5205.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___162_5205.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___162_5205.FStar_TypeChecker_Env.implicits}))))));
)
end)))


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____5223 = (

let uu____5228 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____5229 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____5228), (uu____5229))))
in (match (uu____5223) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (

let uu____5238 = (

let uu____5239 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (

let uu____5240 = (

let uu____5241 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5242 = (

let uu____5245 = (FStar_Syntax_Syntax.as_arg yexp)
in (uu____5245)::[])
in (uu____5241)::uu____5242))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5239 uu____5240)))
in (uu____5238 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let x_eq_y_yret = (

let uu____5251 = (

let uu____5252 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (

let uu____5253 = (

let uu____5254 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5255 = (

let uu____5258 = (

let uu____5259 = (FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5259))
in (

let uu____5260 = (

let uu____5263 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (uu____5263)::[])
in (uu____5258)::uu____5260))
in (uu____5254)::uu____5255))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5252 uu____5253)))
in (uu____5251 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (

let uu____5269 = (

let uu____5270 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (

let uu____5271 = (

let uu____5272 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5273 = (

let uu____5276 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5277 = (

let uu____5280 = (

let uu____5281 = (

let uu____5282 = (

let uu____5283 = (FStar_Syntax_Syntax.mk_binder y)
in (uu____5283)::[])
in (FStar_Syntax_Util.abs uu____5282 x_eq_y_yret (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5281))
in (uu____5280)::[])
in (uu____5276)::uu____5277))
in (uu____5272)::uu____5273))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5270 uu____5271)))
in (uu____5269 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (

let uu____5290 = (FStar_TypeChecker_Env.get_range env)
in (bind uu____5290 env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp comp) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun uu____5313 -> (

let uu____5314 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5314) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end
| uu____5316 -> begin
(

let uu____5317 = (

let uu____5342 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (

let uu____5343 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____5342 uu____5343)))
in (match (uu____5317) with
| ((md, uu____5345, uu____5346), (u_res_t, res_t, wp_then), (uu____5350, uu____5351, wp_else)) -> begin
(

let ifthenelse = (fun md1 res_t1 g wp_t wp_e -> (

let uu____5389 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____5390 = (

let uu____5391 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md1 md1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____5392 = (

let uu____5393 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____5394 = (

let uu____5397 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____5398 = (

let uu____5401 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____5402 = (

let uu____5405 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____5405)::[])
in (uu____5401)::uu____5402))
in (uu____5397)::uu____5398))
in (uu____5393)::uu____5394))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5391 uu____5392)))
in (uu____5390 FStar_Pervasives_Native.None uu____5389))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let uu____5411 = (

let uu____5412 = (FStar_Options.split_cases ())
in (uu____5412 > (Prims.parse_int "0")))
in (match (uu____5411) with
| true -> begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end
| uu____5414 -> begin
(

let wp1 = (

let uu____5418 = (

let uu____5419 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____5420 = (

let uu____5421 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5422 = (

let uu____5425 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5425)::[])
in (uu____5421)::uu____5422))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5419 uu____5420)))
in (uu____5418 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end))
end)))
in (

let uu____5428 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____5428; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____5437 = (

let uu____5438 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____5438))
in (FStar_Syntax_Syntax.fvar uu____5437 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____5473 -> (match (uu____5473) with
| (uu____5478, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun uu____5483 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____5485 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5485) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____5486 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____5505 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____5506 = (

let uu____5507 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____5508 = (

let uu____5509 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____5510 = (

let uu____5513 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____5514 = (

let uu____5517 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____5518 = (

let uu____5521 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____5521)::[])
in (uu____5517)::uu____5518))
in (uu____5513)::uu____5514))
in (uu____5509)::uu____5510))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5507 uu____5508)))
in (uu____5506 FStar_Pervasives_Native.None uu____5505))))
in (

let default_case = (

let post_k = (

let uu____5528 = (

let uu____5535 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____5535)::[])
in (

let uu____5536 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5528 uu____5536)))
in (

let kwp = (

let uu____5542 = (

let uu____5549 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____5549)::[])
in (

let uu____5550 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5542 uu____5550)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____5555 = (

let uu____5556 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____5556)::[])
in (

let uu____5557 = (

let uu____5558 = (

let uu____5561 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____5561))
in (

let uu____5562 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____5558 uu____5562)))
in (FStar_Syntax_Util.abs uu____5555 uu____5557 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun uu____5586 celse -> (match (uu____5586) with
| (g, cthen) -> begin
(

let uu____5594 = (

let uu____5619 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____5619 celse))
in (match (uu____5594) with
| ((md, uu____5621, uu____5622), (uu____5623, uu____5624, wp_then), (uu____5626, uu____5627, wp_else)) -> begin
(

let uu____5647 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____5647 []))
end))
end)) lcases default_case)
in (

let uu____5648 = (

let uu____5649 = (FStar_Options.split_cases ())
in (uu____5649 > (Prims.parse_int "0")))
in (match (uu____5648) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| uu____5650 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____5653 = (destruct_comp comp1)
in (match (uu____5653) with
| (uu____5660, uu____5661, wp) -> begin
(

let wp1 = (

let uu____5666 = (

let uu____5667 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____5668 = (

let uu____5669 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5670 = (

let uu____5673 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5673)::[])
in (uu____5669)::uu____5670))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5667 uu____5668)))
in (uu____5666 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end)))))
end))))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let flags = (

let uu____5691 = (((

let uu____5694 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____5694))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (

let uu____5696 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____5696))))
in (match (uu____5691) with
| true -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____5699 -> begin
lc.FStar_Syntax_Syntax.cflags
end))
in (

let refine1 = (fun uu____5705 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____5709 = (((

let uu____5712 = (is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name)
in (not (uu____5712))) || (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ)) || env.FStar_TypeChecker_Env.lax)
in (match (uu____5709) with
| true -> begin
c
end
| uu____5715 -> begin
(

let uu____5716 = (FStar_Syntax_Util.is_partial_return c)
in (match (uu____5716) with
| true -> begin
c
end
| uu____5719 -> begin
(

let uu____5720 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____5720) with
| true -> begin
(

let uu____5723 = (

let uu____5724 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (not (uu____5724)))
in (match (uu____5723) with
| true -> begin
(

let uu____5727 = (

let uu____5728 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____5729 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" uu____5728 uu____5729)))
in (failwith uu____5727))
end
| uu____5732 -> begin
(

let retc = (return_value env (FStar_Syntax_Util.comp_result c) e)
in (

let uu____5734 = (

let uu____5735 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____5735)))
in (match (uu____5734) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___163_5740 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___163_5740.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___163_5740.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___163_5740.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____5741 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags)
end)))
end))
end
| uu____5742 -> begin
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

let uu____5751 = (

let uu____5754 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____5754 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5751))
in (

let eq1 = (

let uu____5758 = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Util.mk_eq2 uu____5758 t xexp e))
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____5760 = (

let uu____5761 = (

let uu____5766 = (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp c2) ((FStar_Pervasives_Native.Some (x)), (eq_ret)))
in uu____5766.FStar_Syntax_Syntax.comp)
in (uu____5761 ()))
in (FStar_Syntax_Util.comp_set_flags uu____5760 flags))))))))))
end))
end))
end))))
in (

let uu____5769 = (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ)
in (match (uu____5769) with
| true -> begin
lc
end
| uu____5770 -> begin
(

let uu___164_5771 = lc
in {FStar_Syntax_Syntax.eff_name = uu___164_5771.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___164_5771.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine1})
end)))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____5800 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____5800) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5809 = (

let uu____5810 = (

let uu____5815 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____5816 = (FStar_TypeChecker_Env.get_range env)
in ((uu____5815), (uu____5816))))
in FStar_Errors.Error (uu____5810))
in (FStar_Exn.raise uu____5809))
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____5853 = (

let uu____5854 = (FStar_Syntax_Subst.compress t2)
in uu____5854.FStar_Syntax_Syntax.n)
in (match (uu____5853) with
| FStar_Syntax_Syntax.Tm_type (uu____5857) -> begin
true
end
| uu____5858 -> begin
false
end))))
in (

let uu____5859 = (

let uu____5860 = (FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ)
in uu____5860.FStar_Syntax_Syntax.n)
in (match (uu____5859) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____5868 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let lc1 = (

let uu____5879 = (

let uu____5880 = (

let uu____5881 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5881))
in ((FStar_Pervasives_Native.None), (uu____5880)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____5879))
in (

let e1 = (

let uu____5891 = (

let uu____5892 = (

let uu____5893 = (FStar_Syntax_Syntax.as_arg e)
in (uu____5893)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5892))
in (uu____5891 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____5898 -> begin
((e), (lc))
end))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____5931 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____5931) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____5954 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____5976 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5976), (false)))
end
| uu____5981 -> begin
(

let uu____5982 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5982), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____5993) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____6002 = (

let uu____6003 = (

let uu____6008 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in ((uu____6008), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____6003))
in (FStar_Exn.raise uu____6002))
end
| uu____6015 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___165_6018 = lc
in {FStar_Syntax_Syntax.eff_name = uu___165_6018.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___165_6018.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___165_6018.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____6023 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____6023) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___166_6031 = lc
in {FStar_Syntax_Syntax.eff_name = uu___166_6031.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___166_6031.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___166_6031.FStar_Syntax_Syntax.comp})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___167_6034 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___167_6034.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___167_6034.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___167_6034.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____6040 -> (

let uu____6041 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____6041) with
| true -> begin
(lc.FStar_Syntax_Syntax.comp ())
end
| uu____6044 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in (

let uu____6046 = (

let uu____6047 = (FStar_Syntax_Subst.compress f1)
in uu____6047.FStar_Syntax_Syntax.n)
in (match (uu____6046) with
| FStar_Syntax_Syntax.Tm_abs (uu____6052, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6054; FStar_Syntax_Syntax.vars = uu____6055}, uu____6056) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___168_6078 = lc
in {FStar_Syntax_Syntax.eff_name = uu___168_6078.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___168_6078.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___168_6078.FStar_Syntax_Syntax.comp})
in (lc1.FStar_Syntax_Syntax.comp ()))
end
| uu____6079 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in ((

let uu____6084 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6084) with
| true -> begin
(

let uu____6085 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____6086 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____6087 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____6088 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____6085 uu____6086 uu____6087 uu____6088)))))
end
| uu____6089 -> begin
()
end));
(

let ct = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____6091 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____6091) with
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

let uu____6104 = (destruct_comp ct)
in (match (uu____6104) with
| (u_t, uu____6114, uu____6115) -> begin
(

let wp = (

let uu____6119 = (

let uu____6120 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (

let uu____6121 = (

let uu____6122 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6123 = (

let uu____6126 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____6126)::[])
in (uu____6122)::uu____6123))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6120 uu____6121)))
in (uu____6119 FStar_Pervasives_Native.None xexp.FStar_Syntax_Syntax.pos))
in (

let cret = (

let uu____6130 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6130))
in (

let guard = (match (apply_guard1) with
| true -> begin
(

let uu____6140 = (

let uu____6141 = (

let uu____6142 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____6142)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____6141))
in (uu____6140 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____6145 -> begin
f1
end)
in (

let uu____6146 = (

let uu____6151 = (FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____6164 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____6165 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____6151 uu____6164 e cret uu____6165))))
in (match (uu____6146) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___169_6171 = x
in {FStar_Syntax_Syntax.ppname = uu___169_6171.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___169_6171.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____6173 = (

let uu____6174 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6174))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____6173 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (c1.FStar_Syntax_Syntax.comp ())
in ((

let uu____6185 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6185) with
| true -> begin
(

let uu____6186 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____6186))
end
| uu____6187 -> begin
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

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___130_6196 -> (match (uu___130_6196) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____6199 -> begin
[]
end))))
in (

let lc1 = (

let uu___170_6201 = lc
in (

let uu____6202 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____6202; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g2 = (

let uu___171_6204 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___171_6204.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___171_6204.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___171_6204.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____6229 = (

let uu____6230 = (

let uu____6231 = (

let uu____6232 = (

let uu____6233 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____6233))
in (uu____6232)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____6231))
in (uu____6230 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____6229))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____6240 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____6240) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____6251 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____6258) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____6273) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____6302))::((ens, uu____6304))::uu____6305 -> begin
(

let uu____6334 = (

let uu____6337 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____6337))
in (

let uu____6338 = (

let uu____6339 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____6339))
in ((uu____6334), (uu____6338))))
end
| uu____6342 -> begin
(

let uu____6351 = (

let uu____6352 = (

let uu____6357 = (

let uu____6358 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____6358))
in ((uu____6357), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____6352))
in (FStar_Exn.raise uu____6351))
end)
end
| uu____6365 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____6374))::uu____6375 -> begin
(

let uu____6394 = (

let uu____6399 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6399))
in (match (uu____6394) with
| (us_r, uu____6431) -> begin
(

let uu____6432 = (

let uu____6437 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6437))
in (match (uu____6432) with
| (us_e, uu____6469) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____6472 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6472 us_r))
in (

let as_ens = (

let uu____6474 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6474 us_e))
in (

let req = (

let uu____6478 = (

let uu____6479 = (

let uu____6480 = (

let uu____6491 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6491)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____6480)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____6479))
in (uu____6478 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____6509 = (

let uu____6510 = (

let uu____6511 = (

let uu____6522 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6522)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____6511)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____6510))
in (uu____6509 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____6537 = (

let uu____6540 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____6540))
in (

let uu____6541 = (

let uu____6542 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____6542))
in ((uu____6537), (uu____6541)))))))))
end))
end))
end
| uu____6545 -> begin
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

let uu____6573 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6573) with
| true -> begin
(

let uu____6574 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6575 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6574 uu____6575)))
end
| uu____6576 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____6596 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6596) with
| true -> begin
(

let uu____6597 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6598 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6597 uu____6598)))
end
| uu____6599 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____6604 = (

let uu____6605 = (

let uu____6606 = (FStar_Syntax_Subst.compress t)
in uu____6606.FStar_Syntax_Syntax.n)
in (match (uu____6605) with
| FStar_Syntax_Syntax.Tm_app (uu____6609) -> begin
false
end
| uu____6624 -> begin
true
end))
in (match (uu____6604) with
| true -> begin
t
end
| uu____6625 -> begin
(

let uu____6626 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6626) with
| (head1, args) -> begin
(

let uu____6663 = (

let uu____6664 = (

let uu____6665 = (FStar_Syntax_Subst.compress head1)
in uu____6665.FStar_Syntax_Syntax.n)
in (match (uu____6664) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____6668 -> begin
false
end))
in (match (uu____6663) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____6690 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____6699 -> begin
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
| uu____6725 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____6730 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____6730) with
| (formals, uu____6744) -> begin
(

let n_implicits = (

let uu____6762 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____6838 -> (match (uu____6838) with
| (uu____6845, imp) -> begin
((Prims.op_Equality imp FStar_Pervasives_Native.None) || (Prims.op_Equality imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality))))
end))))
in (match (uu____6762) with
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

let uu____6976 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6976) with
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

let uu____7000 = (

let uu____7001 = (

let uu____7006 = (

let uu____7007 = (FStar_Util.string_of_int n_expected)
in (

let uu____7014 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7015 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____7007 uu____7014 uu____7015))))
in (

let uu____7022 = (FStar_TypeChecker_Env.get_range env)
in ((uu____7006), (uu____7022))))
in FStar_Errors.Error (uu____7001))
in (FStar_Exn.raise uu____7000))
end
| uu____7025 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___131_7043 -> (match (uu___131_7043) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7073 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7073) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_41), uu____7182) when (_0_41 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____7225, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____7258 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____7258) with
| (v1, uu____7298, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____7315 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____7315) with
| (args, bs3, subst3, g') -> begin
(

let uu____7408 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____7408)))
end)))
end)))
end
| (uu____7435, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____7481 = (

let uu____7508 = (inst_n_binders t)
in (aux [] uu____7508 bs1))
in (match (uu____7481) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____7579) -> begin
((e), (torig), (guard))
end
| (uu____7610, []) when (

let uu____7641 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____7641))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____7642 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____7674 -> begin
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
| uu____7689 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____7698 = (

let uu____7701 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____7701 (FStar_List.map (fun u -> (

let uu____7711 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____7711 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____7698 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____7730 = (FStar_Util.set_is_empty x)
in (match (uu____7730) with
| true -> begin
[]
end
| uu____7733 -> begin
(

let s = (

let uu____7737 = (

let uu____7740 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____7740))
in (FStar_All.pipe_right uu____7737 FStar_Util.set_elements))
in ((

let uu____7748 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7748) with
| true -> begin
(

let uu____7749 = (

let uu____7750 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____7750))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____7749))
end
| uu____7753 -> begin
()
end));
(

let r = (

let uu____7757 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____7757))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____7772 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7772) with
| true -> begin
(

let uu____7773 = (

let uu____7774 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7774))
in (

let uu____7775 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____7776 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____7773 uu____7775 uu____7776))))
end
| uu____7777 -> begin
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

let uu____7800 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____7800 FStar_Util.fifo_set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____7835) -> begin
generalized_univ_names
end
| (uu____7842, []) -> begin
explicit_univ_names
end
| uu____7849 -> begin
(

let uu____7858 = (

let uu____7859 = (

let uu____7864 = (

let uu____7865 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____7865))
in ((uu____7864), (t.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____7859))
in (FStar_Exn.raise uu____7858))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in (

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____7884 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7884) with
| true -> begin
(

let uu____7885 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____7885))
end
| uu____7886 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____7891 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7891) with
| true -> begin
(

let uu____7892 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" uu____7892))
end
| uu____7893 -> begin
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


let gen : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list FStar_Pervasives_Native.option = (fun env is_rec lecs -> (

let uu____7965 = (

let uu____7966 = (FStar_Util.for_all (fun uu____7979 -> (match (uu____7979) with
| (uu____7988, uu____7989, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____7966))
in (match (uu____7965) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8029 -> begin
(

let norm1 = (fun c -> ((

let uu____8035 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8035) with
| true -> begin
(

let uu____8036 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____8036))
end
| uu____8037 -> begin
()
end));
(

let c1 = (

let uu____8039 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____8039) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
| uu____8040 -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end))
in ((

let uu____8042 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8042) with
| true -> begin
(

let uu____8043 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8043))
end
| uu____8044 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____8104 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____8104 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____8234 -> (match (uu____8234) with
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

let uu____8300 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8300) with
| true -> begin
(

let uu____8301 = (

let uu____8302 = (

let uu____8305 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____8305 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8302 (FStar_String.concat ", ")))
in (

let uu____8332 = (

let uu____8333 = (

let uu____8336 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____8336 (FStar_List.map (fun uu____8364 -> (match (uu____8364) with
| (u, t2) -> begin
(

let uu____8371 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____8372 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s : %s)" uu____8371 uu____8372)))
end)))))
in (FStar_All.pipe_right uu____8333 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8301 uu____8332)))
end
| uu____8375 -> begin
()
end));
(

let univs2 = (

let uu____8379 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uu____8402 -> (match (uu____8402) with
| (uu____8411, t2) -> begin
(

let uu____8413 = (FStar_Syntax_Free.univs t2)
in (FStar_Util.set_union univs2 uu____8413))
end)) univs1 uu____8379))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____8436 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8436) with
| true -> begin
(

let uu____8437 = (

let uu____8438 = (

let uu____8441 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____8441 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8438 (FStar_String.concat ", ")))
in (

let uu____8468 = (

let uu____8469 = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____8501 -> (match (uu____8501) with
| (u, t2) -> begin
(

let uu____8508 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____8509 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "(%s : %s)" uu____8508 uu____8509)))
end))))
in (FStar_All.pipe_right uu____8469 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8437 uu____8468)))
end
| uu____8512 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
))))))
end))
in (

let uu____8539 = (

let uu____8572 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____8572))
in (match (uu____8539) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____8690 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____8690) with
| true -> begin
()
end
| uu____8691 -> begin
(

let uu____8692 = lec_hd
in (match (uu____8692) with
| (lb1, uu____8700, uu____8701) -> begin
(

let uu____8702 = lec2
in (match (uu____8702) with
| (lb2, uu____8710, uu____8711) -> begin
(

let msg = (

let uu____8713 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8714 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____8713 uu____8714)))
in (

let uu____8715 = (

let uu____8716 = (

let uu____8721 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____8721)))
in FStar_Errors.Error (uu____8716))
in (FStar_Exn.raise uu____8715)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun uu____8832 -> (match (uu____8832) with
| (u, uu____8840) -> begin
(FStar_All.pipe_right u21 (FStar_Util.for_some (fun uu____8862 -> (match (uu____8862) with
| (u', uu____8870) -> begin
(FStar_Syntax_Unionfind.equiv u u')
end))))
end)))))
in (

let uu____8875 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____8875) with
| true -> begin
()
end
| uu____8876 -> begin
(

let uu____8877 = lec_hd
in (match (uu____8877) with
| (lb1, uu____8885, uu____8886) -> begin
(

let uu____8887 = lec2
in (match (uu____8887) with
| (lb2, uu____8895, uu____8896) -> begin
(

let msg = (

let uu____8898 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8899 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____8898 uu____8899)))
in (

let uu____8900 = (

let uu____8901 = (

let uu____8906 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____8906)))
in FStar_Errors.Error (uu____8901))
in (FStar_Exn.raise uu____8900)))
end))
end))
end))))
in (

let lecs1 = (

let uu____8916 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____8975 = (univs_and_uvars_of_lec this_lec)
in (match (uu____8975) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____8916 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail = (fun k -> (

let uu____9128 = lec_hd
in (match (uu____9128) with
| (lbname, e, c) -> begin
(

let uu____9138 = (

let uu____9139 = (

let uu____9144 = (

let uu____9145 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9146 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____9147 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____9145 uu____9146 uu____9147))))
in (

let uu____9148 = (FStar_TypeChecker_Env.get_range env)
in ((uu____9144), (uu____9148))))
in FStar_Errors.Error (uu____9139))
in (FStar_Exn.raise uu____9138))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun uu____9178 -> (match (uu____9178) with
| (u, k) -> begin
(

let uu____9191 = (FStar_Syntax_Unionfind.find u)
in (match (uu____9191) with
| FStar_Pervasives_Native.Some (uu____9200) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____9207 -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env k)
in (

let uu____9211 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____9211) with
| (bs, kres) -> begin
((

let uu____9249 = (

let uu____9250 = (

let uu____9253 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____9253))
in uu____9250.FStar_Syntax_Syntax.n)
in (match (uu____9249) with
| FStar_Syntax_Syntax.Tm_type (uu____9254) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____9258 = (

let uu____9259 = (FStar_Util.set_is_empty free)
in (not (uu____9259)))
in (match (uu____9258) with
| true -> begin
(fail kres)
end
| uu____9260 -> begin
()
end)))
end
| uu____9261 -> begin
(fail kres)
end));
(

let a = (

let uu____9263 = (

let uu____9266 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____9266))
in (FStar_Syntax_Syntax.new_bv uu____9263 kres))
in (

let t = (

let uu____9270 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____9270 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
in ((FStar_Syntax_Util.set_uvar u t);
((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)));
)));
)
end)))
end))
end))))))
in (

let gen_univs1 = (gen_univs env univs1)
in (

let gen_tvars = (gen_types uvs)
in (

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____9389 -> (match (uu____9389) with
| (lbname, e, c) -> begin
(

let uu____9435 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____9504 -> begin
(

let uu____9519 = ((e), (c))
in (match (uu____9519) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____9556 -> (match (uu____9556) with
| (x, uu____9564) -> begin
(

let uu____9569 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____9569))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____9579 = (

let uu____9580 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____9580))
in (match (uu____9579) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____9583 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____9584 -> begin
e1
end)
in (

let t = (

let uu____9588 = (

let uu____9589 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____9589.FStar_Syntax_Syntax.n)
in (match (uu____9588) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____9612 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____9612) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____9627 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____9629 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____9629), (gen_tvars))))))))
end))
end)
in (match (uu____9435) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____9778 = (Obj.magic (()))
in ());
(

let uu____9780 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____9780) with
| true -> begin
(

let uu____9781 = (

let uu____9782 = (FStar_List.map (fun uu____9795 -> (match (uu____9795) with
| (lb, uu____9803, uu____9804) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____9782 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____9781))
end
| uu____9807 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____9825 -> (match (uu____9825) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____9854 = (gen env is_rec lecs)
in (match (uu____9854) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____9953 -> (match (uu____9953) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____10015 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____10015) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____10059 -> (match (uu____10059) with
| (l, us, e, c, gvs) -> begin
(

let uu____10093 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____10094 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____10095 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____10096 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____10097 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____10093 uu____10094 uu____10095 uu____10096 uu____10097))))))
end))))
end
| uu____10098 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____10138 -> (match (uu____10138) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____10182 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____10182), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____10228 -> begin
(

let uu____10229 = (FStar_TypeChecker_Rel.try_subtype env2 t11 t21)
in (match (uu____10229) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____10235 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____10235))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____10242 = (

let uu____10243 = (FStar_Syntax_Subst.compress e1)
in uu____10243.FStar_Syntax_Syntax.n)
in (match (uu____10242) with
| FStar_Syntax_Syntax.Tm_name (uu____10246) -> begin
true
end
| uu____10247 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___172_10263 = x
in {FStar_Syntax_Syntax.ppname = uu___172_10263.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___172_10263.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____10264 -> begin
e2
end)))
in (

let env2 = (

let uu___173_10266 = env1
in (

let uu____10267 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___173_10266.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___173_10266.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___173_10266.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___173_10266.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___173_10266.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___173_10266.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___173_10266.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___173_10266.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___173_10266.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___173_10266.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___173_10266.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___173_10266.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___173_10266.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___173_10266.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___173_10266.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____10267; FStar_TypeChecker_Env.is_iface = uu___173_10266.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___173_10266.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___173_10266.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___173_10266.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___173_10266.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___173_10266.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___173_10266.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___173_10266.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___173_10266.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___173_10266.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___173_10266.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___173_10266.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___173_10266.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___173_10266.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___173_10266.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___173_10266.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___173_10266.FStar_TypeChecker_Env.dsenv}))
in (

let uu____10268 = (check env2 t1 t2)
in (match (uu____10268) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10275 = (

let uu____10276 = (

let uu____10281 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____10282 = (FStar_TypeChecker_Env.get_range env2)
in ((uu____10281), (uu____10282))))
in FStar_Errors.Error (uu____10276))
in (FStar_Exn.raise uu____10275))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____10289 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____10289) with
| true -> begin
(

let uu____10290 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____10290))
end
| uu____10291 -> begin
()
end));
(

let uu____10292 = (decorate e t2)
in ((uu____10292), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____10323 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____10323) with
| true -> begin
(

let uu____10328 = (discharge g1)
in (

let uu____10329 = (lc.FStar_Syntax_Syntax.comp ())
in ((uu____10328), (uu____10329))))
end
| uu____10334 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c1 = (

let uu____10342 = (

let uu____10343 = (

let uu____10344 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____10344 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____10343 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____10342 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____10346 = (destruct_comp c1)
in (match (uu____10346) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____10363 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____10364 = (

let uu____10365 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____10366 = (

let uu____10367 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____10368 = (

let uu____10371 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____10371)::[])
in (uu____10367)::uu____10368))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10365 uu____10366)))
in (uu____10364 FStar_Pervasives_Native.None uu____10363)))
in ((

let uu____10375 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10375) with
| true -> begin
(

let uu____10376 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____10376))
end
| uu____10377 -> begin
()
end));
(

let g2 = (

let uu____10379 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____10379))
in (

let uu____10380 = (discharge g2)
in (

let uu____10381 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____10380), (uu____10381)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___132_10407 -> (match (uu___132_10407) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____10415))::[] -> begin
(f fst1)
end
| uu____10432 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____10437 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____10437 (fun _0_44 -> FStar_TypeChecker_Common.NonTrivial (_0_44)))))
in (

let op_or_e = (fun e -> (

let uu____10446 = (

let uu____10449 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____10449))
in (FStar_All.pipe_right uu____10446 (fun _0_45 -> FStar_TypeChecker_Common.NonTrivial (_0_45)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_46 -> FStar_TypeChecker_Common.NonTrivial (_0_46))))
in (

let op_or_t = (fun t -> (

let uu____10460 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____10460 (fun _0_47 -> FStar_TypeChecker_Common.NonTrivial (_0_47)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_48 -> FStar_TypeChecker_Common.NonTrivial (_0_48))))
in (

let short_op_ite = (fun uu___133_10474 -> (match (uu___133_10474) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____10482))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____10501))::[] -> begin
(

let uu____10530 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____10530 (fun _0_49 -> FStar_TypeChecker_Common.NonTrivial (_0_49))))
end
| uu____10535 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____10545 = (

let uu____10552 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____10552)))
in (

let uu____10557 = (

let uu____10566 = (

let uu____10573 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____10573)))
in (

let uu____10578 = (

let uu____10587 = (

let uu____10594 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____10594)))
in (

let uu____10599 = (

let uu____10608 = (

let uu____10615 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____10615)))
in (

let uu____10620 = (

let uu____10629 = (

let uu____10636 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____10636)))
in (uu____10629)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____10608)::uu____10620))
in (uu____10587)::uu____10599))
in (uu____10566)::uu____10578))
in (uu____10545)::uu____10557))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10687 = (FStar_Util.find_map table (fun uu____10700 -> (match (uu____10700) with
| (x, mk1) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
(

let uu____10717 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____10717))
end
| uu____10718 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (uu____10687) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____10720 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____10725 = (

let uu____10726 = (FStar_Syntax_Util.un_uinst l)
in uu____10726.FStar_Syntax_Syntax.n)
in (match (uu____10725) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____10730 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____10756))::uu____10757 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____10768 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____10775, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10776))))::uu____10777 -> begin
bs
end
| uu____10794 -> begin
(

let uu____10795 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____10795) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____10799 = (

let uu____10800 = (FStar_Syntax_Subst.compress t)
in uu____10800.FStar_Syntax_Syntax.n)
in (match (uu____10799) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____10804) -> begin
(

let uu____10821 = (FStar_Util.prefix_until (fun uu___134_10861 -> (match (uu___134_10861) with
| (uu____10868, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10869))) -> begin
false
end
| uu____10872 -> begin
true
end)) bs')
in (match (uu____10821) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____10907, uu____10908) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____10980, uu____10981) -> begin
(

let uu____11054 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____11072 -> (match (uu____11072) with
| (x, uu____11080) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____11054) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____11127 -> (match (uu____11127) with
| (x, i) -> begin
(

let uu____11146 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____11146), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____11155 -> begin
bs
end))
end))
end
| uu____11156 -> begin
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
| uu____11179 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____11197 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____11197) with
| true -> begin
e
end
| uu____11198 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____11224 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____11224) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(

let uu____11226 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) uu____11226));
)
end
| uu____11227 -> begin
()
end));
(

let fv = (

let uu____11229 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____11229 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____11237 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___174_11243 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___174_11243.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___174_11243.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___174_11243.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___174_11243.FStar_Syntax_Syntax.sigattrs})), (uu____11237)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___135_11255 -> (match (uu___135_11255) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11256 -> begin
false
end))
in (

let reducibility = (fun uu___136_11260 -> (match (uu___136_11260) with
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
| uu____11261 -> begin
false
end))
in (

let assumption = (fun uu___137_11265 -> (match (uu___137_11265) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____11266 -> begin
false
end))
in (

let reification = (fun uu___138_11270 -> (match (uu___138_11270) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____11271) -> begin
true
end
| uu____11272 -> begin
false
end))
in (

let inferred = (fun uu___139_11276 -> (match (uu___139_11276) with
| FStar_Syntax_Syntax.Discriminator (uu____11277) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____11278) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____11283) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____11292) -> begin
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
| uu____11301 -> begin
false
end))
in (

let has_eq = (fun uu___140_11305 -> (match (uu___140_11305) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____11306 -> begin
false
end))
in (

let quals_combo_ok = (fun quals q -> (match (q) with
| FStar_Syntax_Syntax.Assumption -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (inferred x)) || (visibility x)) || (assumption x)) || (env.FStar_TypeChecker_Env.is_iface && (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction))))))
end
| FStar_Syntax_Syntax.New -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((Prims.op_Equality x q) || (inferred x)) || (visibility x)) || (assumption x)))))
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (visibility x)) || (reducibility x)) || (reification x)) || (inferred x)) || (env.FStar_TypeChecker_Env.is_iface && (Prims.op_Equality x FStar_Syntax_Syntax.Assumption))))))
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Visible_default -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Irreducible -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Abstract -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Noeq -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.Unopteq -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.TotalEffect -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((Prims.op_Equality x q) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Logic -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)) || (inferred x)) || (visibility x)) || (reducibility x)))))
end
| FStar_Syntax_Syntax.Reifiable -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Reflectable (uu____11366) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11371 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____11375 = (

let uu____11376 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___141_11380 -> (match (uu___141_11380) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____11381 -> begin
false
end))))
in (FStar_All.pipe_right uu____11376 Prims.op_Negation))
in (match (uu____11375) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____11394 = (

let uu____11395 = (

let uu____11400 = (

let uu____11401 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____11401 msg))
in ((uu____11400), (r)))
in FStar_Errors.Error (uu____11395))
in (FStar_Exn.raise uu____11394)))
in (

let err1 = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____11409 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err1 "duplicate qualifiers")
end
| uu____11411 -> begin
()
end);
(

let uu____11413 = (

let uu____11414 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____11414)))
in (match (uu____11413) with
| true -> begin
(err1 "ill-formed combination")
end
| uu____11417 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____11419), uu____11420) -> begin
((

let uu____11436 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____11436) with
| true -> begin
(err1 "recursive definitions cannot be marked inline")
end
| uu____11439 -> begin
()
end));
(

let uu____11440 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____11440) with
| true -> begin
(err1 "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____11445 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____11446) -> begin
(

let uu____11455 = (

let uu____11456 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____11456)))
in (match (uu____11455) with
| true -> begin
(err'1 ())
end
| uu____11461 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____11462) -> begin
(

let uu____11469 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____11469) with
| true -> begin
(err'1 ())
end
| uu____11472 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____11473) -> begin
(

let uu____11480 = (

let uu____11481 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____11481)))
in (match (uu____11480) with
| true -> begin
(err'1 ())
end
| uu____11486 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____11487) -> begin
(

let uu____11488 = (

let uu____11489 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11489)))
in (match (uu____11488) with
| true -> begin
(err'1 ())
end
| uu____11494 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____11495) -> begin
(

let uu____11496 = (

let uu____11497 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11497)))
in (match (uu____11496) with
| true -> begin
(err'1 ())
end
| uu____11502 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____11503) -> begin
(

let uu____11516 = (

let uu____11517 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____11517)))
in (match (uu____11516) with
| true -> begin
(err'1 ())
end
| uu____11522 -> begin
()
end))
end
| uu____11523 -> begin
()
end);
))))))
end
| uu____11524 -> begin
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

let uu____11596 = (

let uu____11599 = (

let uu____11600 = (

let uu____11607 = (

let uu____11608 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____11608))
in ((uu____11607), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____11600))
in (FStar_Syntax_Syntax.mk uu____11599))
in (uu____11596 FStar_Pervasives_Native.None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____11649 -> (match (uu____11649) with
| (x, imp) -> begin
(

let uu____11660 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____11660), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args FStar_Pervasives_Native.None p)))
in (

let unrefined_arg_binder = (

let uu____11662 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____11662))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____11664 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____11671 = (

let uu____11672 = (

let uu____11673 = (

let uu____11674 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____11675 = (

let uu____11676 = (

let uu____11677 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11677))
in (uu____11676)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____11674 uu____11675)))
in (uu____11673 FStar_Pervasives_Native.None p))
in (FStar_Syntax_Util.b2t uu____11672))
in (FStar_Syntax_Util.refine x uu____11671)))
in (

let uu____11680 = (

let uu___175_11681 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___175_11681.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___175_11681.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____11680)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____11696 = (FStar_List.map (fun uu____11718 -> (match (uu____11718) with
| (x, uu____11730) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____11696 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____11779 -> (match (uu____11779) with
| (x, uu____11791) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____11799 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((

let uu____11805 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____11805)) || (

let uu____11807 = (

let uu____11808 = (FStar_TypeChecker_Env.current_module env)
in uu____11808.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____11807)))
in (

let quals = (

let uu____11812 = (

let uu____11815 = (

let uu____11818 = (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit))
in (match (uu____11818) with
| true -> begin
(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____11821 -> begin
[]
end))
in (

let uu____11822 = (FStar_List.filter (fun uu___142_11826 -> (match (uu___142_11826) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11827 -> begin
false
end)) iquals)
in (FStar_List.append uu____11815 uu____11822)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::[]
end
| uu____11830 -> begin
[]
end)) uu____11812))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____11848 = (

let uu____11849 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____11849))
in (FStar_Syntax_Syntax.mk_Total uu____11848))
in (

let uu____11850 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____11850)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid discriminator_name); FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((

let uu____11853 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____11853) with
| true -> begin
(

let uu____11854 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____11854))
end
| uu____11855 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____11858 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____11864 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____11907 -> (match (uu____11907) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____11931 = (

let uu____11934 = (

let uu____11935 = (

let uu____11942 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____11942), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____11935))
in (pos uu____11934))
in ((uu____11931), (b)))
end
| uu____11945 -> begin
(

let uu____11946 = (

let uu____11949 = (

let uu____11950 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____11950))
in (pos uu____11949))
in ((uu____11946), (b)))
end))
end))))
in (

let pat_true = (

let uu____11968 = (

let uu____11971 = (

let uu____11972 = (

let uu____11985 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____11985), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____11972))
in (pos uu____11971))
in ((uu____11968), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_true_bool)))
in (

let pat_false = (

let uu____12019 = (

let uu____12022 = (

let uu____12023 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____12023))
in (pos uu____12022))
in ((uu____12019), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst unrefined_arg_binder))
in (

let uu____12035 = (

let uu____12038 = (

let uu____12039 = (

let uu____12062 = (

let uu____12065 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____12066 = (

let uu____12069 = (FStar_Syntax_Util.branch pat_false)
in (uu____12069)::[])
in (uu____12065)::uu____12066))
in ((arg_exp), (uu____12062)))
in FStar_Syntax_Syntax.Tm_match (uu____12039))
in (FStar_Syntax_Syntax.mk uu____12038))
in (uu____12035 FStar_Pervasives_Native.None p))))))
end)
in (

let dd = (

let uu____12076 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____12076) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____12079 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____12082 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____12084 = (

let uu____12089 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____12089))
in (

let uu____12090 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____12084; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____12090}))
in (

let impl = (

let uu____12094 = (

let uu____12095 = (

let uu____12102 = (

let uu____12105 = (

let uu____12106 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____12106 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____12105)::[])
in ((((false), ((lb)::[]))), (uu____12102)))
in FStar_Syntax_Syntax.Sig_let (uu____12095))
in {FStar_Syntax_Syntax.sigel = uu____12094; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____12124 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12124) with
| true -> begin
(

let uu____12125 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____12125))
end
| uu____12126 -> begin
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

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____12167 -> (match (uu____12167) with
| (a, uu____12173) -> begin
(

let uu____12174 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____12174) with
| (field_name, uu____12180) -> begin
(

let field_proj_tm = (

let uu____12182 = (

let uu____12183 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____12183))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____12182 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) FStar_Pervasives_Native.None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____12200 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____12232 -> (match (uu____12232) with
| (x, uu____12240) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____12242 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____12242) with
| (field_name, uu____12250) -> begin
(

let t = (

let uu____12252 = (

let uu____12253 = (

let uu____12256 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____12256))
in (FStar_Syntax_Util.arrow binders uu____12253))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____12252))
in (

let only_decl = ((

let uu____12260 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____12260)) || (

let uu____12262 = (

let uu____12263 = (FStar_TypeChecker_Env.current_module env)
in uu____12263.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____12262)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____12277 = (FStar_List.filter (fun uu___143_12281 -> (match (uu___143_12281) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____12282 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____12277)
end
| uu____12283 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___144_12295 -> (match (uu___144_12295) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____12296 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let attrs = (match (only_decl) with
| true -> begin
[]
end
| uu____12308 -> begin
(FStar_Syntax_Util.attr_substitute)::[]
end)
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs}
in ((

let uu____12315 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12315) with
| true -> begin
(

let uu____12316 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____12316))
end
| uu____12317 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____12320 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____12364 -> (match (uu____12364) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((Prims.op_Equality (i + ntps) j)) with
| true -> begin
(

let uu____12388 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____12388), (b)))
end
| uu____12393 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____12404 = (

let uu____12407 = (

let uu____12408 = (

let uu____12415 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____12415), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____12408))
in (pos uu____12407))
in ((uu____12404), (b)))
end
| uu____12418 -> begin
(

let uu____12419 = (

let uu____12422 = (

let uu____12423 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____12423))
in (pos uu____12422))
in ((uu____12419), (b)))
end)
end))
end))))
in (

let pat = (

let uu____12439 = (

let uu____12442 = (

let uu____12443 = (

let uu____12456 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____12456), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____12443))
in (pos uu____12442))
in (

let uu____12465 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____12439), (FStar_Pervasives_Native.None), (uu____12465))))
in (

let body = (

let uu____12477 = (

let uu____12480 = (

let uu____12481 = (

let uu____12504 = (

let uu____12507 = (FStar_Syntax_Util.branch pat)
in (uu____12507)::[])
in ((arg_exp), (uu____12504)))
in FStar_Syntax_Syntax.Tm_match (uu____12481))
in (FStar_Syntax_Syntax.mk uu____12480))
in (uu____12477 FStar_Pervasives_Native.None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let dd = (

let uu____12515 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____12515) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____12518 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____12520 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____12522 = (

let uu____12527 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____12527))
in (

let uu____12528 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____12522; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____12528}))
in (

let impl = (

let uu____12532 = (

let uu____12533 = (

let uu____12540 = (

let uu____12543 = (

let uu____12544 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____12544 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____12543)::[])
in ((((false), ((lb)::[]))), (uu____12540)))
in FStar_Syntax_Syntax.Sig_let (uu____12533))
in {FStar_Syntax_Syntax.sigel = uu____12532; FStar_Syntax_Syntax.sigrng = p1; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____12562 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12562) with
| true -> begin
(

let uu____12563 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____12563))
end
| uu____12564 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____12567 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
))))))))
end)))
end))))
in (FStar_All.pipe_right uu____12200 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, uu____12607) when (not ((FStar_Ident.lid_equals constr_lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____12612 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____12612) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____12634 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____12634) with
| (formals, uu____12650) -> begin
(

let uu____12667 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____12699 = (

let uu____12700 = (

let uu____12701 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____12701))
in (FStar_Ident.lid_equals typ_lid uu____12700))
in (match (uu____12699) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____12720, uvs', tps, typ0, uu____12724, constrs) -> begin
FStar_Pervasives_Native.Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____12743 -> begin
(failwith "Impossible")
end)
end
| uu____12752 -> begin
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
| uu____12802 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____12667) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____12816 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____12816) with
| (indices, uu____12832) -> begin
(

let refine_domain = (

let uu____12850 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___145_12855 -> (match (uu___145_12855) with
| FStar_Syntax_Syntax.RecordConstructor (uu____12856) -> begin
true
end
| uu____12865 -> begin
false
end))))
in (match (uu____12850) with
| true -> begin
false
end
| uu____12866 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___146_12873 -> (match (uu___146_12873) with
| FStar_Syntax_Syntax.RecordConstructor (uu____12876, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____12888 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____12889 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____12889) with
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
| uu____12898 -> begin
iquals
end)
in (

let fields = (

let uu____12900 = (FStar_Util.first_N n_typars formals)
in (match (uu____12900) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____12965 uu____12966 -> (match (((uu____12965), (uu____12966))) with
| ((x, uu____12984), (x', uu____12986)) -> begin
(

let uu____12995 = (

let uu____13002 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____13002)))
in FStar_Syntax_Syntax.NT (uu____12995))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____13003 -> begin
[]
end))




