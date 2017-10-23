
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

let m = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (

let uu____4359 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4359) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____4360 -> begin
(

let uu____4361 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____4361) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____4369 = (

let uu____4370 = (

let uu____4371 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____4372 = (

let uu____4373 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____4374 = (

let uu____4377 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____4377)::[])
in (uu____4373)::uu____4374))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4371 uu____4372)))
in (uu____4370 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env uu____4369)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
in ((

let uu____4381 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____4381) with
| true -> begin
(

let uu____4382 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____4383 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____4384 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4382 uu____4383 uu____4384))))
end
| uu____4385 -> begin
()
end));
c;
)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____4407 -> (match (uu____4407) with
| (b, lc2) -> begin
(

let lc11 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc21 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc11 lc21)
in ((

let uu____4420 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4420) with
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

let uu____4423 = (match (e1opt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (

let uu____4425 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____4426 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" uu____4423 uu____4425 bstr uu____4426)))))
end
| uu____4427 -> begin
()
end));
(

let bind_it = (fun uu____4431 -> (

let uu____4432 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4432) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____4434 -> begin
(

let c1 = (lc11.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc21.FStar_Syntax_Syntax.comp ())
in ((

let uu____4442 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4442) with
| true -> begin
(

let uu____4443 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____4445 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____4446 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____4447 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (

let uu____4448 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" uu____4443 uu____4445 uu____4446 uu____4447 uu____4448))))))
end
| uu____4449 -> begin
()
end));
(

let try_simplify = (fun uu____4463 -> (

let aux = (fun uu____4477 -> (

let uu____4478 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____4478) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____4507) -> begin
(

let uu____4508 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____4508) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____4527 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____4534 -> begin
(

let uu____4535 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____4535) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____4554 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____4591 = (

let uu____4596 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____4596), (reason)))
in FStar_Util.Inl (uu____4591))
end
| uu____4601 -> begin
(aux ())
end))
in (

let rec maybe_close = (fun t x c -> (

let uu____4620 = (

let uu____4621 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in uu____4621.FStar_Syntax_Syntax.n)
in (match (uu____4620) with
| FStar_Syntax_Syntax.Tm_refine (y, uu____4625) -> begin
(maybe_close y.FStar_Syntax_Syntax.sort x c)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____4631 -> begin
c
end)))
in (

let uu____4632 = (

let uu____4633 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____4633))
in (match (uu____4632) with
| true -> begin
(

let uu____4646 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____4646) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____4665 -> begin
(

let uu____4666 = (

let uu____4667 = (

let uu____4672 = (FStar_TypeChecker_Env.get_range env)
in (("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad"), (uu____4672)))
in FStar_Errors.Error (uu____4667))
in (FStar_Exn.raise uu____4666))
end))
end
| uu____4683 -> begin
(

let uu____4684 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____4684) with
| true -> begin
(subst_c2 "both total")
end
| uu____4695 -> begin
(

let uu____4696 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____4696) with
| true -> begin
(

let uu____4707 = (

let uu____4712 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____4712), ("both gtot")))
in FStar_Util.Inl (uu____4707))
end
| uu____4717 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____4738 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____4740 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____4740))))
in (match (uu____4738) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___158_4753 = x
in {FStar_Syntax_Syntax.ppname = uu___158_4753.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_4753.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____4754 = (

let uu____4759 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____4759), ("c1 Tot")))
in FStar_Util.Inl (uu____4754))))
end
| uu____4764 -> begin
(aux ())
end))
end
| uu____4765 -> begin
(aux ())
end)
end))
end))
end))))))
in (

let uu____4774 = (try_simplify ())
in (match (uu____4774) with
| FStar_Util.Inl (c, reason) -> begin
((

let uu____4798 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4798) with
| true -> begin
(

let uu____4799 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____4800 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____4801 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print4 "Simplified (because %s) bind %s %s to %s\n" reason uu____4799 uu____4800 uu____4801))))
end
| uu____4802 -> begin
()
end));
c;
)
end
| FStar_Util.Inr (reason) -> begin
(

let uu____4810 = (lift_and_destruct env c1 c2)
in (match (uu____4810) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4867 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____4867)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____4869 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4869)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____4882 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____4883 = (

let uu____4886 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____4887 = (

let uu____4890 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____4891 = (

let uu____4894 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____4895 = (

let uu____4898 = (

let uu____4899 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____4899))
in (uu____4898)::[])
in (uu____4894)::uu____4895))
in (uu____4890)::uu____4891))
in (uu____4886)::uu____4887))
in (uu____4882)::uu____4883))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (

let uu____4904 = (

let uu____4905 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____4905 wp_args))
in (uu____4904 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
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

let uu____4952 = (

let uu____4953 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____4953))
in (match (uu____4952) with
| true -> begin
f
end
| uu____4954 -> begin
(

let uu____4955 = (reason1 ())
in (label uu____4955 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___159_4969 = g
in (

let uu____4970 = (

let uu____4971 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____4971))
in {FStar_TypeChecker_Env.guard_f = uu____4970; FStar_TypeChecker_Env.deferred = uu___159_4969.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___159_4969.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___159_4969.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____4983 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____5005 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____5009 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5009) with
| true -> begin
c
end
| uu____5012 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____5016 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____5016) with
| true -> begin
c
end
| uu____5019 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____5021 = (destruct_comp c1)
in (match (uu____5021) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5037 = (

let uu____5038 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____5039 = (

let uu____5040 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5041 = (

let uu____5044 = (FStar_Syntax_Syntax.as_arg f1)
in (

let uu____5045 = (

let uu____5048 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5048)::[])
in (uu____5044)::uu____5045))
in (uu____5040)::uu____5041))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5038 uu____5039)))
in (uu____5037 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 c1.FStar_Syntax_Syntax.flags)))
end)))
end))
end)
end))))
in (

let uu___160_5051 = lc
in {FStar_Syntax_Syntax.eff_name = uu___160_5051.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___160_5051.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___160_5051.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> (

let uu____5089 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____5089) with
| true -> begin
((lc), (g0))
end
| uu____5094 -> begin
((

let uu____5096 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5096) with
| true -> begin
(

let uu____5097 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____5098 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" uu____5097 uu____5098)))
end
| uu____5099 -> begin
()
end));
(

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___129_5108 -> (match (uu___129_5108) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| uu____5111 -> begin
[]
end))))
in (

let strengthen = (fun uu____5117 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____5123 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____5125 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____5125) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c1 = (

let uu____5132 = ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (

let uu____5134 = (FStar_Syntax_Util.is_partial_return c)
in (not (uu____5134))))
in (match (uu____5132) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" FStar_Pervasives_Native.None (FStar_Syntax_Util.comp_result c))
in (

let xret = (

let uu____5141 = (

let uu____5142 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort uu____5142))
in (FStar_Syntax_Util.comp_set_flags uu____5141 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc1 = (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc1.FStar_Syntax_Syntax.comp ()))))
end
| uu____5146 -> begin
c
end))
in ((

let uu____5148 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5148) with
| true -> begin
(

let uu____5149 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____5150 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____5149 uu____5150)))
end
| uu____5151 -> begin
()
end));
(

let c2 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____5153 = (destruct_comp c2)
in (match (uu____5153) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5169 = (

let uu____5170 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____5171 = (

let uu____5172 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5173 = (

let uu____5176 = (

let uu____5177 = (

let uu____5178 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____5178 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5177))
in (

let uu____5179 = (

let uu____5182 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5182)::[])
in (uu____5176)::uu____5179))
in (uu____5172)::uu____5173))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5170 uu____5171)))
in (uu____5169 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in ((

let uu____5186 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5186) with
| true -> begin
(

let uu____5187 = (FStar_Syntax_Print.term_to_string wp1)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" uu____5187))
end
| uu____5188 -> begin
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

let uu____5190 = (

let uu___161_5191 = lc
in (

let uu____5192 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____5193 = (

let uu____5196 = ((FStar_Syntax_Util.is_pure_lcomp lc) && (

let uu____5198 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation uu____5198)))
in (match (uu____5196) with
| true -> begin
flags
end
| uu____5201 -> begin
[]
end))
in {FStar_Syntax_Syntax.eff_name = uu____5192; FStar_Syntax_Syntax.res_typ = uu___161_5191.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu____5193; FStar_Syntax_Syntax.comp = strengthen})))
in ((uu____5190), ((

let uu___162_5203 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___162_5203.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___162_5203.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___162_5203.FStar_TypeChecker_Env.implicits}))))));
)
end)))


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____5221 = (

let uu____5226 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____5227 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____5226), (uu____5227))))
in (match (uu____5221) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (

let uu____5236 = (

let uu____5237 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (

let uu____5238 = (

let uu____5239 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5240 = (

let uu____5243 = (FStar_Syntax_Syntax.as_arg yexp)
in (uu____5243)::[])
in (uu____5239)::uu____5240))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5237 uu____5238)))
in (uu____5236 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let x_eq_y_yret = (

let uu____5249 = (

let uu____5250 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (

let uu____5251 = (

let uu____5252 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5253 = (

let uu____5256 = (

let uu____5257 = (FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5257))
in (

let uu____5258 = (

let uu____5261 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (uu____5261)::[])
in (uu____5256)::uu____5258))
in (uu____5252)::uu____5253))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5250 uu____5251)))
in (uu____5249 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (

let uu____5267 = (

let uu____5268 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (

let uu____5269 = (

let uu____5270 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5271 = (

let uu____5274 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5275 = (

let uu____5278 = (

let uu____5279 = (

let uu____5280 = (

let uu____5281 = (FStar_Syntax_Syntax.mk_binder y)
in (uu____5281)::[])
in (FStar_Syntax_Util.abs uu____5280 x_eq_y_yret (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5279))
in (uu____5278)::[])
in (uu____5274)::uu____5275))
in (uu____5270)::uu____5271))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5268 uu____5269)))
in (uu____5267 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (

let uu____5288 = (FStar_TypeChecker_Env.get_range env)
in (bind uu____5288 env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp comp) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun uu____5311 -> (

let uu____5312 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5312) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end
| uu____5314 -> begin
(

let uu____5315 = (

let uu____5340 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (

let uu____5341 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____5340 uu____5341)))
in (match (uu____5315) with
| ((md, uu____5343, uu____5344), (u_res_t, res_t, wp_then), (uu____5348, uu____5349, wp_else)) -> begin
(

let ifthenelse = (fun md1 res_t1 g wp_t wp_e -> (

let uu____5387 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____5388 = (

let uu____5389 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md1 md1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____5390 = (

let uu____5391 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____5392 = (

let uu____5395 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____5396 = (

let uu____5399 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____5400 = (

let uu____5403 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____5403)::[])
in (uu____5399)::uu____5400))
in (uu____5395)::uu____5396))
in (uu____5391)::uu____5392))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5389 uu____5390)))
in (uu____5388 FStar_Pervasives_Native.None uu____5387))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let uu____5409 = (

let uu____5410 = (FStar_Options.split_cases ())
in (uu____5410 > (Prims.parse_int "0")))
in (match (uu____5409) with
| true -> begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end
| uu____5412 -> begin
(

let wp1 = (

let uu____5416 = (

let uu____5417 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____5418 = (

let uu____5419 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5420 = (

let uu____5423 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5423)::[])
in (uu____5419)::uu____5420))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5417 uu____5418)))
in (uu____5416 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end))
end)))
in (

let uu____5426 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____5426; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____5435 = (

let uu____5436 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____5436))
in (FStar_Syntax_Syntax.fvar uu____5435 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____5471 -> (match (uu____5471) with
| (uu____5476, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun uu____5481 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____5483 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5483) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____5484 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____5503 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____5504 = (

let uu____5505 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____5506 = (

let uu____5507 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____5508 = (

let uu____5511 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____5512 = (

let uu____5515 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____5516 = (

let uu____5519 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____5519)::[])
in (uu____5515)::uu____5516))
in (uu____5511)::uu____5512))
in (uu____5507)::uu____5508))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5505 uu____5506)))
in (uu____5504 FStar_Pervasives_Native.None uu____5503))))
in (

let default_case = (

let post_k = (

let uu____5526 = (

let uu____5533 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____5533)::[])
in (

let uu____5534 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5526 uu____5534)))
in (

let kwp = (

let uu____5540 = (

let uu____5547 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____5547)::[])
in (

let uu____5548 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5540 uu____5548)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____5553 = (

let uu____5554 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____5554)::[])
in (

let uu____5555 = (

let uu____5556 = (

let uu____5559 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____5559))
in (

let uu____5560 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____5556 uu____5560)))
in (FStar_Syntax_Util.abs uu____5553 uu____5555 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun uu____5584 celse -> (match (uu____5584) with
| (g, cthen) -> begin
(

let uu____5592 = (

let uu____5617 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____5617 celse))
in (match (uu____5592) with
| ((md, uu____5619, uu____5620), (uu____5621, uu____5622, wp_then), (uu____5624, uu____5625, wp_else)) -> begin
(

let uu____5645 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____5645 []))
end))
end)) lcases default_case)
in (

let uu____5646 = (

let uu____5647 = (FStar_Options.split_cases ())
in (uu____5647 > (Prims.parse_int "0")))
in (match (uu____5646) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| uu____5648 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____5651 = (destruct_comp comp1)
in (match (uu____5651) with
| (uu____5658, uu____5659, wp) -> begin
(

let wp1 = (

let uu____5664 = (

let uu____5665 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____5666 = (

let uu____5667 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5668 = (

let uu____5671 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5671)::[])
in (uu____5667)::uu____5668))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5665 uu____5666)))
in (uu____5664 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end)))))
end))))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let flags = (

let uu____5689 = (((

let uu____5692 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____5692))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (

let uu____5694 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____5694))))
in (match (uu____5689) with
| true -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____5697 -> begin
lc.FStar_Syntax_Syntax.cflags
end))
in (

let refine1 = (fun uu____5703 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____5707 = ((

let uu____5710 = (is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name)
in (not (uu____5710))) || env.FStar_TypeChecker_Env.lax)
in (match (uu____5707) with
| true -> begin
c
end
| uu____5713 -> begin
(

let uu____5714 = (FStar_Syntax_Util.is_partial_return c)
in (match (uu____5714) with
| true -> begin
c
end
| uu____5717 -> begin
(

let uu____5718 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____5718) with
| true -> begin
(

let uu____5721 = (

let uu____5722 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (not (uu____5722)))
in (match (uu____5721) with
| true -> begin
(

let uu____5725 = (

let uu____5726 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____5727 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" uu____5726 uu____5727)))
in (failwith uu____5725))
end
| uu____5730 -> begin
(

let retc = (return_value env (FStar_Syntax_Util.comp_result c) e)
in (

let uu____5732 = (

let uu____5733 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____5733)))
in (match (uu____5732) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___163_5738 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___163_5738.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___163_5738.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___163_5738.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____5739 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags)
end)))
end))
end
| uu____5740 -> begin
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

let uu____5749 = (

let uu____5752 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____5752 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5749))
in (

let eq1 = (

let uu____5756 = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Util.mk_eq2 uu____5756 t xexp e))
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____5758 = (

let uu____5759 = (

let uu____5764 = (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp c2) ((FStar_Pervasives_Native.Some (x)), (eq_ret)))
in uu____5764.FStar_Syntax_Syntax.comp)
in (uu____5759 ()))
in (FStar_Syntax_Util.comp_set_flags uu____5758 flags))))))))))
end))
end))
end))))
in (

let uu___164_5767 = lc
in {FStar_Syntax_Syntax.eff_name = uu___164_5767.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___164_5767.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine1}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____5796 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____5796) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5805 = (

let uu____5806 = (

let uu____5811 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____5812 = (FStar_TypeChecker_Env.get_range env)
in ((uu____5811), (uu____5812))))
in FStar_Errors.Error (uu____5806))
in (FStar_Exn.raise uu____5805))
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____5849 = (

let uu____5850 = (FStar_Syntax_Subst.compress t2)
in uu____5850.FStar_Syntax_Syntax.n)
in (match (uu____5849) with
| FStar_Syntax_Syntax.Tm_type (uu____5853) -> begin
true
end
| uu____5854 -> begin
false
end))))
in (

let uu____5855 = (

let uu____5856 = (FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ)
in uu____5856.FStar_Syntax_Syntax.n)
in (match (uu____5855) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____5864 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let lc1 = (

let uu____5875 = (

let uu____5876 = (

let uu____5877 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5877))
in ((FStar_Pervasives_Native.None), (uu____5876)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____5875))
in (

let e1 = (

let uu____5887 = (

let uu____5888 = (

let uu____5889 = (FStar_Syntax_Syntax.as_arg e)
in (uu____5889)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5888))
in (uu____5887 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____5894 -> begin
((e), (lc))
end))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____5927 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____5927) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____5950 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____5972 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5972), (false)))
end
| uu____5977 -> begin
(

let uu____5978 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5978), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____5989) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____5998 = (

let uu____5999 = (

let uu____6004 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in ((uu____6004), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____5999))
in (FStar_Exn.raise uu____5998))
end
| uu____6011 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___165_6014 = lc
in {FStar_Syntax_Syntax.eff_name = uu___165_6014.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___165_6014.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___165_6014.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____6019 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____6019) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___166_6027 = lc
in {FStar_Syntax_Syntax.eff_name = uu___166_6027.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___166_6027.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___166_6027.FStar_Syntax_Syntax.comp})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___167_6030 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___167_6030.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___167_6030.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___167_6030.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____6036 -> (

let uu____6037 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____6037) with
| true -> begin
(lc.FStar_Syntax_Syntax.comp ())
end
| uu____6040 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in (

let uu____6042 = (

let uu____6043 = (FStar_Syntax_Subst.compress f1)
in uu____6043.FStar_Syntax_Syntax.n)
in (match (uu____6042) with
| FStar_Syntax_Syntax.Tm_abs (uu____6048, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6050; FStar_Syntax_Syntax.vars = uu____6051}, uu____6052) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___168_6074 = lc
in {FStar_Syntax_Syntax.eff_name = uu___168_6074.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___168_6074.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___168_6074.FStar_Syntax_Syntax.comp})
in (lc1.FStar_Syntax_Syntax.comp ()))
end
| uu____6075 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in ((

let uu____6080 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6080) with
| true -> begin
(

let uu____6081 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____6082 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____6083 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____6084 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____6081 uu____6082 uu____6083 uu____6084)))))
end
| uu____6085 -> begin
()
end));
(

let ct = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____6087 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____6087) with
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

let uu____6100 = (destruct_comp ct)
in (match (uu____6100) with
| (u_t, uu____6110, uu____6111) -> begin
(

let wp = (

let uu____6115 = (

let uu____6116 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (

let uu____6117 = (

let uu____6118 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6119 = (

let uu____6122 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____6122)::[])
in (uu____6118)::uu____6119))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6116 uu____6117)))
in (uu____6115 FStar_Pervasives_Native.None xexp.FStar_Syntax_Syntax.pos))
in (

let cret = (

let uu____6126 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6126))
in (

let guard = (match (apply_guard1) with
| true -> begin
(

let uu____6136 = (

let uu____6137 = (

let uu____6138 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____6138)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____6137))
in (uu____6136 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____6141 -> begin
f1
end)
in (

let uu____6142 = (

let uu____6147 = (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____6160 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____6161 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____6147 uu____6160 e cret uu____6161))))
in (match (uu____6142) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___169_6167 = x
in {FStar_Syntax_Syntax.ppname = uu___169_6167.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___169_6167.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____6169 = (

let uu____6170 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6170))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____6169 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (c1.FStar_Syntax_Syntax.comp ())
in ((

let uu____6181 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6181) with
| true -> begin
(

let uu____6182 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____6182))
end
| uu____6183 -> begin
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

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___130_6192 -> (match (uu___130_6192) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____6195 -> begin
[]
end))))
in (

let lc1 = (

let uu___170_6197 = lc
in (

let uu____6198 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____6198; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g2 = (

let uu___171_6200 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___171_6200.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___171_6200.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___171_6200.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____6225 = (

let uu____6226 = (

let uu____6227 = (

let uu____6228 = (

let uu____6229 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____6229))
in (uu____6228)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____6227))
in (uu____6226 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____6225))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____6236 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____6236) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____6247 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____6254) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____6269) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____6298))::((ens, uu____6300))::uu____6301 -> begin
(

let uu____6330 = (

let uu____6333 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____6333))
in (

let uu____6334 = (

let uu____6335 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____6335))
in ((uu____6330), (uu____6334))))
end
| uu____6338 -> begin
(

let uu____6347 = (

let uu____6348 = (

let uu____6353 = (

let uu____6354 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____6354))
in ((uu____6353), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____6348))
in (FStar_Exn.raise uu____6347))
end)
end
| uu____6361 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____6370))::uu____6371 -> begin
(

let uu____6390 = (

let uu____6395 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6395))
in (match (uu____6390) with
| (us_r, uu____6427) -> begin
(

let uu____6428 = (

let uu____6433 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6433))
in (match (uu____6428) with
| (us_e, uu____6465) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____6468 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6468 us_r))
in (

let as_ens = (

let uu____6470 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6470 us_e))
in (

let req = (

let uu____6474 = (

let uu____6475 = (

let uu____6476 = (

let uu____6487 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6487)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____6476)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____6475))
in (uu____6474 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____6505 = (

let uu____6506 = (

let uu____6507 = (

let uu____6518 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6518)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____6507)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____6506))
in (uu____6505 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____6533 = (

let uu____6536 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____6536))
in (

let uu____6537 = (

let uu____6538 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____6538))
in ((uu____6533), (uu____6537)))))))))
end))
end))
end
| uu____6541 -> begin
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

let uu____6569 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6569) with
| true -> begin
(

let uu____6570 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6571 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6570 uu____6571)))
end
| uu____6572 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____6592 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6592) with
| true -> begin
(

let uu____6593 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6594 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6593 uu____6594)))
end
| uu____6595 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____6600 = (

let uu____6601 = (

let uu____6602 = (FStar_Syntax_Subst.compress t)
in uu____6602.FStar_Syntax_Syntax.n)
in (match (uu____6601) with
| FStar_Syntax_Syntax.Tm_app (uu____6605) -> begin
false
end
| uu____6620 -> begin
true
end))
in (match (uu____6600) with
| true -> begin
t
end
| uu____6621 -> begin
(

let uu____6622 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6622) with
| (head1, args) -> begin
(

let uu____6659 = (

let uu____6660 = (

let uu____6661 = (FStar_Syntax_Subst.compress head1)
in uu____6661.FStar_Syntax_Syntax.n)
in (match (uu____6660) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____6664 -> begin
false
end))
in (match (uu____6659) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____6686 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____6695 -> begin
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
| uu____6721 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____6726 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____6726) with
| (formals, uu____6740) -> begin
(

let n_implicits = (

let uu____6758 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____6834 -> (match (uu____6834) with
| (uu____6841, imp) -> begin
((Prims.op_Equality imp FStar_Pervasives_Native.None) || (Prims.op_Equality imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality))))
end))))
in (match (uu____6758) with
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

let uu____6972 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6972) with
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

let uu____6996 = (

let uu____6997 = (

let uu____7002 = (

let uu____7003 = (FStar_Util.string_of_int n_expected)
in (

let uu____7010 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7011 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____7003 uu____7010 uu____7011))))
in (

let uu____7018 = (FStar_TypeChecker_Env.get_range env)
in ((uu____7002), (uu____7018))))
in FStar_Errors.Error (uu____6997))
in (FStar_Exn.raise uu____6996))
end
| uu____7021 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___131_7039 -> (match (uu___131_7039) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7069 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7069) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_42), uu____7178) when (_0_42 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____7221, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____7254 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____7254) with
| (v1, uu____7294, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____7311 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____7311) with
| (args, bs3, subst3, g') -> begin
(

let uu____7404 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____7404)))
end)))
end)))
end
| (uu____7431, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____7477 = (

let uu____7504 = (inst_n_binders t)
in (aux [] uu____7504 bs1))
in (match (uu____7477) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____7575) -> begin
((e), (torig), (guard))
end
| (uu____7606, []) when (

let uu____7637 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____7637))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____7638 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____7670 -> begin
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
| uu____7685 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____7694 = (

let uu____7697 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____7697 (FStar_List.map (fun u -> (

let uu____7707 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____7707 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____7694 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____7726 = (FStar_Util.set_is_empty x)
in (match (uu____7726) with
| true -> begin
[]
end
| uu____7729 -> begin
(

let s = (

let uu____7733 = (

let uu____7736 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____7736))
in (FStar_All.pipe_right uu____7733 FStar_Util.set_elements))
in ((

let uu____7744 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7744) with
| true -> begin
(

let uu____7745 = (

let uu____7746 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____7746))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____7745))
end
| uu____7749 -> begin
()
end));
(

let r = (

let uu____7753 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____7753))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____7768 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7768) with
| true -> begin
(

let uu____7769 = (

let uu____7770 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7770))
in (

let uu____7771 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____7772 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____7769 uu____7771 uu____7772))))
end
| uu____7773 -> begin
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

let uu____7796 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____7796 FStar_Util.fifo_set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____7831) -> begin
generalized_univ_names
end
| (uu____7838, []) -> begin
explicit_univ_names
end
| uu____7845 -> begin
(

let uu____7854 = (

let uu____7855 = (

let uu____7860 = (

let uu____7861 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____7861))
in ((uu____7860), (t.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____7855))
in (FStar_Exn.raise uu____7854))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in (

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____7880 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7880) with
| true -> begin
(

let uu____7881 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____7881))
end
| uu____7882 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____7887 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7887) with
| true -> begin
(

let uu____7888 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" uu____7888))
end
| uu____7889 -> begin
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

let uu____7961 = (

let uu____7962 = (FStar_Util.for_all (fun uu____7975 -> (match (uu____7975) with
| (uu____7984, uu____7985, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____7962))
in (match (uu____7961) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8025 -> begin
(

let norm1 = (fun c -> ((

let uu____8031 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8031) with
| true -> begin
(

let uu____8032 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____8032))
end
| uu____8033 -> begin
()
end));
(

let c1 = (

let uu____8035 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____8035) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
| uu____8036 -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end))
in ((

let uu____8038 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8038) with
| true -> begin
(

let uu____8039 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8039))
end
| uu____8040 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____8100 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____8100 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____8230 -> (match (uu____8230) with
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

let uu____8296 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8296) with
| true -> begin
(

let uu____8297 = (

let uu____8298 = (

let uu____8301 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____8301 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8298 (FStar_String.concat ", ")))
in (

let uu____8328 = (

let uu____8329 = (

let uu____8332 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____8332 (FStar_List.map (fun uu____8360 -> (match (uu____8360) with
| (u, t2) -> begin
(

let uu____8367 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____8368 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s : %s)" uu____8367 uu____8368)))
end)))))
in (FStar_All.pipe_right uu____8329 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8297 uu____8328)))
end
| uu____8371 -> begin
()
end));
(

let univs2 = (

let uu____8375 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uu____8398 -> (match (uu____8398) with
| (uu____8407, t2) -> begin
(

let uu____8409 = (FStar_Syntax_Free.univs t2)
in (FStar_Util.set_union univs2 uu____8409))
end)) univs1 uu____8375))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____8432 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8432) with
| true -> begin
(

let uu____8433 = (

let uu____8434 = (

let uu____8437 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____8437 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8434 (FStar_String.concat ", ")))
in (

let uu____8464 = (

let uu____8465 = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____8497 -> (match (uu____8497) with
| (u, t2) -> begin
(

let uu____8504 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____8505 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "(%s : %s)" uu____8504 uu____8505)))
end))))
in (FStar_All.pipe_right uu____8465 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8433 uu____8464)))
end
| uu____8508 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
))))))
end))
in (

let uu____8535 = (

let uu____8568 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____8568))
in (match (uu____8535) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____8686 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____8686) with
| true -> begin
()
end
| uu____8687 -> begin
(

let uu____8688 = lec_hd
in (match (uu____8688) with
| (lb1, uu____8696, uu____8697) -> begin
(

let uu____8698 = lec2
in (match (uu____8698) with
| (lb2, uu____8706, uu____8707) -> begin
(

let msg = (

let uu____8709 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8710 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____8709 uu____8710)))
in (

let uu____8711 = (

let uu____8712 = (

let uu____8717 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____8717)))
in FStar_Errors.Error (uu____8712))
in (FStar_Exn.raise uu____8711)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun uu____8828 -> (match (uu____8828) with
| (u, uu____8836) -> begin
(FStar_All.pipe_right u21 (FStar_Util.for_some (fun uu____8858 -> (match (uu____8858) with
| (u', uu____8866) -> begin
(FStar_Syntax_Unionfind.equiv u u')
end))))
end)))))
in (

let uu____8871 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____8871) with
| true -> begin
()
end
| uu____8872 -> begin
(

let uu____8873 = lec_hd
in (match (uu____8873) with
| (lb1, uu____8881, uu____8882) -> begin
(

let uu____8883 = lec2
in (match (uu____8883) with
| (lb2, uu____8891, uu____8892) -> begin
(

let msg = (

let uu____8894 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8895 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____8894 uu____8895)))
in (

let uu____8896 = (

let uu____8897 = (

let uu____8902 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____8902)))
in FStar_Errors.Error (uu____8897))
in (FStar_Exn.raise uu____8896)))
end))
end))
end))))
in (

let lecs1 = (

let uu____8912 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____8971 = (univs_and_uvars_of_lec this_lec)
in (match (uu____8971) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____8912 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail = (fun k -> (

let uu____9124 = lec_hd
in (match (uu____9124) with
| (lbname, e, c) -> begin
(

let uu____9134 = (

let uu____9135 = (

let uu____9140 = (

let uu____9141 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9142 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____9143 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____9141 uu____9142 uu____9143))))
in (

let uu____9144 = (FStar_TypeChecker_Env.get_range env)
in ((uu____9140), (uu____9144))))
in FStar_Errors.Error (uu____9135))
in (FStar_Exn.raise uu____9134))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun uu____9174 -> (match (uu____9174) with
| (u, k) -> begin
(

let uu____9187 = (FStar_Syntax_Unionfind.find u)
in (match (uu____9187) with
| FStar_Pervasives_Native.Some (uu____9196) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____9203 -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env k)
in (

let uu____9207 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____9207) with
| (bs, kres) -> begin
((

let uu____9245 = (

let uu____9246 = (

let uu____9249 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____9249))
in uu____9246.FStar_Syntax_Syntax.n)
in (match (uu____9245) with
| FStar_Syntax_Syntax.Tm_type (uu____9250) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____9254 = (

let uu____9255 = (FStar_Util.set_is_empty free)
in (not (uu____9255)))
in (match (uu____9254) with
| true -> begin
(fail kres)
end
| uu____9256 -> begin
()
end)))
end
| uu____9257 -> begin
(fail kres)
end));
(

let a = (

let uu____9259 = (

let uu____9262 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____9262))
in (FStar_Syntax_Syntax.new_bv uu____9259 kres))
in (

let t = (

let uu____9266 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____9266 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
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

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____9385 -> (match (uu____9385) with
| (lbname, e, c) -> begin
(

let uu____9431 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____9500 -> begin
(

let uu____9515 = ((e), (c))
in (match (uu____9515) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____9552 -> (match (uu____9552) with
| (x, uu____9560) -> begin
(

let uu____9565 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____9565))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____9575 = (

let uu____9576 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____9576))
in (match (uu____9575) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____9579 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____9580 -> begin
e1
end)
in (

let t = (

let uu____9584 = (

let uu____9585 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____9585.FStar_Syntax_Syntax.n)
in (match (uu____9584) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____9608 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____9608) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____9623 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____9625 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____9625), (gen_tvars))))))))
end))
end)
in (match (uu____9431) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____9774 = (Obj.magic (()))
in ());
(

let uu____9776 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____9776) with
| true -> begin
(

let uu____9777 = (

let uu____9778 = (FStar_List.map (fun uu____9791 -> (match (uu____9791) with
| (lb, uu____9799, uu____9800) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____9778 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____9777))
end
| uu____9803 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____9821 -> (match (uu____9821) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____9850 = (gen env is_rec lecs)
in (match (uu____9850) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____9949 -> (match (uu____9949) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____10011 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____10011) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____10055 -> (match (uu____10055) with
| (l, us, e, c, gvs) -> begin
(

let uu____10089 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____10090 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____10091 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____10092 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____10093 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____10089 uu____10090 uu____10091 uu____10092 uu____10093))))))
end))))
end
| uu____10094 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____10134 -> (match (uu____10134) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____10178 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____10178), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____10224 -> begin
(

let uu____10225 = (FStar_TypeChecker_Rel.try_subtype env2 t11 t21)
in (match (uu____10225) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____10231 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44)) uu____10231))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____10238 = (

let uu____10239 = (FStar_Syntax_Subst.compress e1)
in uu____10239.FStar_Syntax_Syntax.n)
in (match (uu____10238) with
| FStar_Syntax_Syntax.Tm_name (uu____10242) -> begin
true
end
| uu____10243 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___172_10259 = x
in {FStar_Syntax_Syntax.ppname = uu___172_10259.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___172_10259.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____10260 -> begin
e2
end)))
in (

let env2 = (

let uu___173_10262 = env1
in (

let uu____10263 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___173_10262.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___173_10262.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___173_10262.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___173_10262.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___173_10262.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___173_10262.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___173_10262.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___173_10262.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___173_10262.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___173_10262.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___173_10262.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___173_10262.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___173_10262.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___173_10262.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___173_10262.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____10263; FStar_TypeChecker_Env.is_iface = uu___173_10262.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___173_10262.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___173_10262.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___173_10262.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___173_10262.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___173_10262.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___173_10262.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___173_10262.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___173_10262.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___173_10262.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___173_10262.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___173_10262.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___173_10262.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___173_10262.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___173_10262.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___173_10262.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___173_10262.FStar_TypeChecker_Env.dsenv}))
in (

let uu____10264 = (check env2 t1 t2)
in (match (uu____10264) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10271 = (

let uu____10272 = (

let uu____10277 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____10278 = (FStar_TypeChecker_Env.get_range env2)
in ((uu____10277), (uu____10278))))
in FStar_Errors.Error (uu____10272))
in (FStar_Exn.raise uu____10271))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____10285 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____10285) with
| true -> begin
(

let uu____10286 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____10286))
end
| uu____10287 -> begin
()
end));
(

let uu____10288 = (decorate e t2)
in ((uu____10288), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____10319 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____10319) with
| true -> begin
(

let uu____10324 = (discharge g1)
in (

let uu____10325 = (lc.FStar_Syntax_Syntax.comp ())
in ((uu____10324), (uu____10325))))
end
| uu____10330 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c1 = (

let uu____10338 = (

let uu____10339 = (

let uu____10340 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____10340 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____10339 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____10338 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____10342 = (destruct_comp c1)
in (match (uu____10342) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____10359 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____10360 = (

let uu____10361 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____10362 = (

let uu____10363 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____10364 = (

let uu____10367 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____10367)::[])
in (uu____10363)::uu____10364))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10361 uu____10362)))
in (uu____10360 FStar_Pervasives_Native.None uu____10359)))
in ((

let uu____10371 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10371) with
| true -> begin
(

let uu____10372 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____10372))
end
| uu____10373 -> begin
()
end));
(

let g2 = (

let uu____10375 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____10375))
in (

let uu____10376 = (discharge g2)
in (

let uu____10377 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____10376), (uu____10377)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___132_10403 -> (match (uu___132_10403) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____10411))::[] -> begin
(f fst1)
end
| uu____10428 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____10433 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____10433 (fun _0_45 -> FStar_TypeChecker_Common.NonTrivial (_0_45)))))
in (

let op_or_e = (fun e -> (

let uu____10442 = (

let uu____10445 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____10445))
in (FStar_All.pipe_right uu____10442 (fun _0_46 -> FStar_TypeChecker_Common.NonTrivial (_0_46)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_47 -> FStar_TypeChecker_Common.NonTrivial (_0_47))))
in (

let op_or_t = (fun t -> (

let uu____10456 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____10456 (fun _0_48 -> FStar_TypeChecker_Common.NonTrivial (_0_48)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_49 -> FStar_TypeChecker_Common.NonTrivial (_0_49))))
in (

let short_op_ite = (fun uu___133_10470 -> (match (uu___133_10470) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____10478))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____10497))::[] -> begin
(

let uu____10526 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____10526 (fun _0_50 -> FStar_TypeChecker_Common.NonTrivial (_0_50))))
end
| uu____10531 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____10541 = (

let uu____10548 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____10548)))
in (

let uu____10553 = (

let uu____10562 = (

let uu____10569 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____10569)))
in (

let uu____10574 = (

let uu____10583 = (

let uu____10590 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____10590)))
in (

let uu____10595 = (

let uu____10604 = (

let uu____10611 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____10611)))
in (

let uu____10616 = (

let uu____10625 = (

let uu____10632 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____10632)))
in (uu____10625)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____10604)::uu____10616))
in (uu____10583)::uu____10595))
in (uu____10562)::uu____10574))
in (uu____10541)::uu____10553))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10683 = (FStar_Util.find_map table (fun uu____10696 -> (match (uu____10696) with
| (x, mk1) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
(

let uu____10713 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____10713))
end
| uu____10714 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (uu____10683) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____10716 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____10721 = (

let uu____10722 = (FStar_Syntax_Util.un_uinst l)
in uu____10722.FStar_Syntax_Syntax.n)
in (match (uu____10721) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____10726 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____10752))::uu____10753 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____10764 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____10771, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10772))))::uu____10773 -> begin
bs
end
| uu____10790 -> begin
(

let uu____10791 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____10791) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____10795 = (

let uu____10796 = (FStar_Syntax_Subst.compress t)
in uu____10796.FStar_Syntax_Syntax.n)
in (match (uu____10795) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____10800) -> begin
(

let uu____10817 = (FStar_Util.prefix_until (fun uu___134_10857 -> (match (uu___134_10857) with
| (uu____10864, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10865))) -> begin
false
end
| uu____10868 -> begin
true
end)) bs')
in (match (uu____10817) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____10903, uu____10904) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____10976, uu____10977) -> begin
(

let uu____11050 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____11068 -> (match (uu____11068) with
| (x, uu____11076) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____11050) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____11123 -> (match (uu____11123) with
| (x, i) -> begin
(

let uu____11142 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____11142), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____11151 -> begin
bs
end))
end))
end
| uu____11152 -> begin
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
| uu____11175 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____11193 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____11193) with
| true -> begin
e
end
| uu____11194 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____11220 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____11220) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(

let uu____11222 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) uu____11222));
)
end
| uu____11223 -> begin
()
end));
(

let fv = (

let uu____11225 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____11225 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____11233 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___174_11239 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___174_11239.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___174_11239.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___174_11239.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___174_11239.FStar_Syntax_Syntax.sigattrs})), (uu____11233)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___135_11251 -> (match (uu___135_11251) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11252 -> begin
false
end))
in (

let reducibility = (fun uu___136_11256 -> (match (uu___136_11256) with
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
| uu____11257 -> begin
false
end))
in (

let assumption = (fun uu___137_11261 -> (match (uu___137_11261) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____11262 -> begin
false
end))
in (

let reification = (fun uu___138_11266 -> (match (uu___138_11266) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____11267) -> begin
true
end
| uu____11268 -> begin
false
end))
in (

let inferred = (fun uu___139_11272 -> (match (uu___139_11272) with
| FStar_Syntax_Syntax.Discriminator (uu____11273) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____11274) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____11279) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____11288) -> begin
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
| uu____11297 -> begin
false
end))
in (

let has_eq = (fun uu___140_11301 -> (match (uu___140_11301) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____11302 -> begin
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
| FStar_Syntax_Syntax.Reflectable (uu____11362) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11367 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____11371 = (

let uu____11372 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___141_11376 -> (match (uu___141_11376) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____11377 -> begin
false
end))))
in (FStar_All.pipe_right uu____11372 Prims.op_Negation))
in (match (uu____11371) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____11390 = (

let uu____11391 = (

let uu____11396 = (

let uu____11397 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____11397 msg))
in ((uu____11396), (r)))
in FStar_Errors.Error (uu____11391))
in (FStar_Exn.raise uu____11390)))
in (

let err1 = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____11405 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err1 "duplicate qualifiers")
end
| uu____11407 -> begin
()
end);
(

let uu____11409 = (

let uu____11410 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____11410)))
in (match (uu____11409) with
| true -> begin
(err1 "ill-formed combination")
end
| uu____11413 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____11415), uu____11416) -> begin
((

let uu____11432 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____11432) with
| true -> begin
(err1 "recursive definitions cannot be marked inline")
end
| uu____11435 -> begin
()
end));
(

let uu____11436 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____11436) with
| true -> begin
(err1 "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____11441 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____11442) -> begin
(

let uu____11451 = (

let uu____11452 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____11452)))
in (match (uu____11451) with
| true -> begin
(err'1 ())
end
| uu____11457 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____11458) -> begin
(

let uu____11465 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____11465) with
| true -> begin
(err'1 ())
end
| uu____11468 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____11469) -> begin
(

let uu____11476 = (

let uu____11477 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____11477)))
in (match (uu____11476) with
| true -> begin
(err'1 ())
end
| uu____11482 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____11483) -> begin
(

let uu____11484 = (

let uu____11485 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11485)))
in (match (uu____11484) with
| true -> begin
(err'1 ())
end
| uu____11490 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____11491) -> begin
(

let uu____11492 = (

let uu____11493 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11493)))
in (match (uu____11492) with
| true -> begin
(err'1 ())
end
| uu____11498 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____11499) -> begin
(

let uu____11512 = (

let uu____11513 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____11513)))
in (match (uu____11512) with
| true -> begin
(err'1 ())
end
| uu____11518 -> begin
()
end))
end
| uu____11519 -> begin
()
end);
))))))
end
| uu____11520 -> begin
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

let uu____11592 = (

let uu____11595 = (

let uu____11596 = (

let uu____11603 = (

let uu____11604 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____11604))
in ((uu____11603), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____11596))
in (FStar_Syntax_Syntax.mk uu____11595))
in (uu____11592 FStar_Pervasives_Native.None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____11645 -> (match (uu____11645) with
| (x, imp) -> begin
(

let uu____11656 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____11656), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args FStar_Pervasives_Native.None p)))
in (

let unrefined_arg_binder = (

let uu____11658 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____11658))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____11660 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____11667 = (

let uu____11668 = (

let uu____11669 = (

let uu____11670 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____11671 = (

let uu____11672 = (

let uu____11673 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11673))
in (uu____11672)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____11670 uu____11671)))
in (uu____11669 FStar_Pervasives_Native.None p))
in (FStar_Syntax_Util.b2t uu____11668))
in (FStar_Syntax_Util.refine x uu____11667)))
in (

let uu____11676 = (

let uu___175_11677 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___175_11677.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___175_11677.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____11676)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____11692 = (FStar_List.map (fun uu____11714 -> (match (uu____11714) with
| (x, uu____11726) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____11692 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____11775 -> (match (uu____11775) with
| (x, uu____11787) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____11795 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((

let uu____11801 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____11801)) || (

let uu____11803 = (

let uu____11804 = (FStar_TypeChecker_Env.current_module env)
in uu____11804.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____11803)))
in (

let quals = (

let uu____11808 = (

let uu____11811 = (

let uu____11814 = (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit))
in (match (uu____11814) with
| true -> begin
(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____11817 -> begin
[]
end))
in (

let uu____11818 = (FStar_List.filter (fun uu___142_11822 -> (match (uu___142_11822) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11823 -> begin
false
end)) iquals)
in (FStar_List.append uu____11811 uu____11818)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::[]
end
| uu____11826 -> begin
[]
end)) uu____11808))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____11844 = (

let uu____11845 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____11845))
in (FStar_Syntax_Syntax.mk_Total uu____11844))
in (

let uu____11846 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____11846)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid discriminator_name); FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((

let uu____11849 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____11849) with
| true -> begin
(

let uu____11850 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____11850))
end
| uu____11851 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____11854 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____11860 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____11903 -> (match (uu____11903) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____11927 = (

let uu____11930 = (

let uu____11931 = (

let uu____11938 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____11938), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____11931))
in (pos uu____11930))
in ((uu____11927), (b)))
end
| uu____11941 -> begin
(

let uu____11942 = (

let uu____11945 = (

let uu____11946 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____11946))
in (pos uu____11945))
in ((uu____11942), (b)))
end))
end))))
in (

let pat_true = (

let uu____11964 = (

let uu____11967 = (

let uu____11968 = (

let uu____11981 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____11981), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____11968))
in (pos uu____11967))
in ((uu____11964), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_true_bool)))
in (

let pat_false = (

let uu____12015 = (

let uu____12018 = (

let uu____12019 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____12019))
in (pos uu____12018))
in ((uu____12015), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst unrefined_arg_binder))
in (

let uu____12031 = (

let uu____12034 = (

let uu____12035 = (

let uu____12058 = (

let uu____12061 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____12062 = (

let uu____12065 = (FStar_Syntax_Util.branch pat_false)
in (uu____12065)::[])
in (uu____12061)::uu____12062))
in ((arg_exp), (uu____12058)))
in FStar_Syntax_Syntax.Tm_match (uu____12035))
in (FStar_Syntax_Syntax.mk uu____12034))
in (uu____12031 FStar_Pervasives_Native.None p))))))
end)
in (

let dd = (

let uu____12072 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____12072) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____12075 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____12078 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____12080 = (

let uu____12085 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____12085))
in (

let uu____12086 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____12080; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____12086}))
in (

let impl = (

let uu____12090 = (

let uu____12091 = (

let uu____12098 = (

let uu____12101 = (

let uu____12102 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____12102 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____12101)::[])
in ((((false), ((lb)::[]))), (uu____12098)))
in FStar_Syntax_Syntax.Sig_let (uu____12091))
in {FStar_Syntax_Syntax.sigel = uu____12090; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____12120 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12120) with
| true -> begin
(

let uu____12121 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____12121))
end
| uu____12122 -> begin
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

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____12163 -> (match (uu____12163) with
| (a, uu____12169) -> begin
(

let uu____12170 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____12170) with
| (field_name, uu____12176) -> begin
(

let field_proj_tm = (

let uu____12178 = (

let uu____12179 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____12179))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____12178 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) FStar_Pervasives_Native.None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____12196 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____12228 -> (match (uu____12228) with
| (x, uu____12236) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____12238 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____12238) with
| (field_name, uu____12246) -> begin
(

let t = (

let uu____12248 = (

let uu____12249 = (

let uu____12252 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____12252))
in (FStar_Syntax_Util.arrow binders uu____12249))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____12248))
in (

let only_decl = ((

let uu____12256 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____12256)) || (

let uu____12258 = (

let uu____12259 = (FStar_TypeChecker_Env.current_module env)
in uu____12259.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____12258)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____12273 = (FStar_List.filter (fun uu___143_12277 -> (match (uu___143_12277) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____12278 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____12273)
end
| uu____12279 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___144_12291 -> (match (uu___144_12291) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____12292 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let attrs = (match (only_decl) with
| true -> begin
[]
end
| uu____12304 -> begin
(FStar_Syntax_Util.attr_substitute)::[]
end)
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs}
in ((

let uu____12311 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12311) with
| true -> begin
(

let uu____12312 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____12312))
end
| uu____12313 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____12316 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____12360 -> (match (uu____12360) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((Prims.op_Equality (i + ntps) j)) with
| true -> begin
(

let uu____12384 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____12384), (b)))
end
| uu____12389 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____12400 = (

let uu____12403 = (

let uu____12404 = (

let uu____12411 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____12411), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____12404))
in (pos uu____12403))
in ((uu____12400), (b)))
end
| uu____12414 -> begin
(

let uu____12415 = (

let uu____12418 = (

let uu____12419 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____12419))
in (pos uu____12418))
in ((uu____12415), (b)))
end)
end))
end))))
in (

let pat = (

let uu____12435 = (

let uu____12438 = (

let uu____12439 = (

let uu____12452 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____12452), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____12439))
in (pos uu____12438))
in (

let uu____12461 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____12435), (FStar_Pervasives_Native.None), (uu____12461))))
in (

let body = (

let uu____12473 = (

let uu____12476 = (

let uu____12477 = (

let uu____12500 = (

let uu____12503 = (FStar_Syntax_Util.branch pat)
in (uu____12503)::[])
in ((arg_exp), (uu____12500)))
in FStar_Syntax_Syntax.Tm_match (uu____12477))
in (FStar_Syntax_Syntax.mk uu____12476))
in (uu____12473 FStar_Pervasives_Native.None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let dd = (

let uu____12511 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____12511) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____12514 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____12516 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____12518 = (

let uu____12523 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____12523))
in (

let uu____12524 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____12518; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____12524}))
in (

let impl = (

let uu____12528 = (

let uu____12529 = (

let uu____12536 = (

let uu____12539 = (

let uu____12540 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____12540 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____12539)::[])
in ((((false), ((lb)::[]))), (uu____12536)))
in FStar_Syntax_Syntax.Sig_let (uu____12529))
in {FStar_Syntax_Syntax.sigel = uu____12528; FStar_Syntax_Syntax.sigrng = p1; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____12558 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12558) with
| true -> begin
(

let uu____12559 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____12559))
end
| uu____12560 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____12563 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
))))))))
end)))
end))))
in (FStar_All.pipe_right uu____12196 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, uu____12603) when (not ((FStar_Ident.lid_equals constr_lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____12608 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____12608) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____12630 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____12630) with
| (formals, uu____12646) -> begin
(

let uu____12663 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____12695 = (

let uu____12696 = (

let uu____12697 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____12697))
in (FStar_Ident.lid_equals typ_lid uu____12696))
in (match (uu____12695) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____12716, uvs', tps, typ0, uu____12720, constrs) -> begin
FStar_Pervasives_Native.Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____12739 -> begin
(failwith "Impossible")
end)
end
| uu____12748 -> begin
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
| uu____12798 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____12663) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____12812 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____12812) with
| (indices, uu____12828) -> begin
(

let refine_domain = (

let uu____12846 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___145_12851 -> (match (uu___145_12851) with
| FStar_Syntax_Syntax.RecordConstructor (uu____12852) -> begin
true
end
| uu____12861 -> begin
false
end))))
in (match (uu____12846) with
| true -> begin
false
end
| uu____12862 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___146_12869 -> (match (uu___146_12869) with
| FStar_Syntax_Syntax.RecordConstructor (uu____12872, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____12884 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____12885 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____12885) with
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
| uu____12894 -> begin
iquals
end)
in (

let fields = (

let uu____12896 = (FStar_Util.first_N n_typars formals)
in (match (uu____12896) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____12961 uu____12962 -> (match (((uu____12961), (uu____12962))) with
| ((x, uu____12980), (x', uu____12982)) -> begin
(

let uu____12991 = (

let uu____12998 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____12998)))
in FStar_Syntax_Syntax.NT (uu____12991))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____12999 -> begin
[]
end))




