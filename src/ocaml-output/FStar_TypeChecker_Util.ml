
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  unit = (fun env errs -> (

let uu____21 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____22 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.log_issue uu____21 uu____22))))


let new_implicit_var_aux : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.binding Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun reason r gamma binders k -> (

let ctx_uvar = (

let uu____67 = (FStar_Syntax_Unionfind.fresh ())
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____67; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = binders; FStar_Syntax_Syntax.ctx_uvar_typ = k; FStar_Syntax_Syntax.ctx_uvar_reason = reason; FStar_Syntax_Syntax.ctx_uvar_should_check = true; FStar_Syntax_Syntax.ctx_uvar_range = r})
in ((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true gamma binders);
(

let uu____79 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_uvar)) FStar_Pervasives_Native.None r)
in ((ctx_uvar), (uu____79)));
)))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (

let uu____116 = (FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid)
in (match (uu____116) with
| FStar_Pervasives_Native.Some ((uu____139)::((tm, uu____141))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| uu____191 -> begin
(

let binders = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____203 = (new_implicit_var_aux reason r env.FStar_TypeChecker_Env.gamma binders k)
in (match (uu____203) with
| (ctx_uvar, t) -> begin
(

let g = (

let uu___98_229 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___98_229.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___98_229.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___98_229.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (((reason), (t), (ctx_uvar), (r), (true)))::[]})
in ((t), ((((ctx_uvar), (r)))::[]), (g)))
end)))
end)))


let close_guard_implicits : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env xs g -> (

let rec aux = (fun x i -> (

let uu____328 = i
in (match (uu____328) with
| (reason, term, ctx_u, range, should_check) -> begin
(match ((not (should_check))) with
| true -> begin
i
end
| uu____374 -> begin
(

let uu____375 = (FStar_Syntax_Unionfind.find ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____375) with
| FStar_Pervasives_Native.Some (uu____390) -> begin
i
end
| FStar_Pervasives_Native.None -> begin
(

let uu____391 = (FStar_Util.prefix_until (fun uu___79_406 -> (match (uu___79_406) with
| FStar_Syntax_Syntax.Binding_var (uu____407) -> begin
true
end
| uu____408 -> begin
false
end)) ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma)
in (match (uu____391) with
| FStar_Pervasives_Native.None -> begin
i
end
| FStar_Pervasives_Native.Some (uu____431, hd1, gamma_tail) -> begin
((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason range should_check ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders);
(match (hd1) with
| FStar_Syntax_Syntax.Binding_var (x') when (FStar_Syntax_Syntax.bv_eq x x') -> begin
(

let uu____466 = (FStar_Util.prefix ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____466) with
| (binders_pfx, uu____498) -> begin
(

let typ = (

let uu____522 = (

let uu____529 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____529)::[])
in (

let uu____542 = (FStar_Syntax_Syntax.mk_Total ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Syntax_Util.arrow uu____522 uu____542)))
in (

let uu____545 = (new_implicit_var_aux reason range gamma_tail binders_pfx typ)
in (match (uu____545) with
| (ctx_v, t_v) -> begin
(

let sol = (

let uu____573 = (

let uu____578 = (

let uu____579 = (

let uu____586 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____586))
in (uu____579)::[])
in (FStar_Syntax_Syntax.mk_Tm_app t_v uu____578))
in (uu____573 FStar_Pervasives_Native.None range))
in ((

let uu____602 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____602) with
| true -> begin
(

let uu____603 = (FStar_Syntax_Print.ctx_uvar_to_string ctx_u)
in (

let uu____604 = (FStar_Syntax_Print.term_to_string sol)
in (FStar_Util.print2 "Closing implicits %s to %s" uu____603 uu____604)))
end
| uu____605 -> begin
()
end));
(FStar_Syntax_Unionfind.change ctx_u.FStar_Syntax_Syntax.ctx_uvar_head sol);
((reason), (t_v), (ctx_v), (range), (should_check));
))
end)))
end))
end
| uu____609 -> begin
i
end);
)
end))
end))
end)
end)))
in (

let uu____610 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred (FStar_List.partition (fun uu____632 -> (match (uu____632) with
| (uu____637, p) -> begin
(FStar_TypeChecker_Rel.flex_prob_closing env xs p)
end))))
in (match (uu____610) with
| (solve_now, defer) -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env (

let uu___99_643 = g
in {FStar_TypeChecker_Env.guard_f = uu___99_643.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = solve_now; FStar_TypeChecker_Env.univ_ineqs = uu___99_643.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___99_643.FStar_TypeChecker_Env.implicits}))
in (

let g2 = (

let uu___100_645 = g1
in {FStar_TypeChecker_Env.guard_f = uu___100_645.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = defer; FStar_TypeChecker_Env.univ_ineqs = uu___100_645.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___100_645.FStar_TypeChecker_Env.implicits})
in (

let is = (FStar_List.fold_left (fun is uu____684 -> (match (uu____684) with
| (x, uu____718) -> begin
(FStar_List.map (aux x) is)
end)) g2.FStar_TypeChecker_Env.implicits xs)
in (

let g3 = (

let uu___101_744 = g2
in {FStar_TypeChecker_Env.guard_f = uu___101_744.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___101_744.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___101_744.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = is})
in ((

let uu____746 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____746) with
| true -> begin
(

let uu____747 = (FStar_TypeChecker_Rel.guard_to_string env g3)
in (FStar_Util.print1 "Closed implicits, guard is\n\t%s\n" uu____747))
end
| uu____748 -> begin
()
end));
g3;
)))))
end))))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____762 = (

let uu____763 = (FStar_Util.set_is_empty uvs)
in (not (uu____763)))
in (match (uu____762) with
| true -> begin
(

let us = (

let uu____765 = (

let uu____768 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun u -> (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)) uu____768))
in (FStar_All.pipe_right uu____765 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____779 = (

let uu____784 = (

let uu____785 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____785))
in ((FStar_Errors.Error_UncontrainedUnificationVar), (uu____784)))
in (FStar_Errors.log_issue r uu____779));
(FStar_Options.pop ());
))
end
| uu____786 -> begin
()
end))))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool * FStar_TypeChecker_Env.guard_t) = (fun env uu____804 -> (match (uu____804) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____816; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____818; FStar_Syntax_Syntax.lbpos = uu____819} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____856 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 e)
in (match (uu____856) with
| (univ_vars2, e1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars2)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let mk_binder1 = (fun env2 a -> (

let uu____892 = (

let uu____893 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in uu____893.FStar_Syntax_Syntax.n)
in (match (uu____892) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____902 = (FStar_Syntax_Util.type_u ())
in (match (uu____902) with
| (k, uu____914) -> begin
(

let uu____915 = (new_implicit_var "" e1.FStar_Syntax_Syntax.pos env2 k)
in (match (uu____915) with
| (t2, uu____935, guard) -> begin
(((

let uu___102_950 = a
in {FStar_Syntax_Syntax.ppname = uu___102_950.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_950.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (false), (guard))
end))
end))
end
| uu____951 -> begin
((a), (true), (FStar_TypeChecker_Rel.trivial_guard))
end)))
in (

let rec aux = (fun must_check_ty env2 e2 g -> (

let e3 = (FStar_Syntax_Subst.compress e2)
in (match (e3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e4, uu____1005) -> begin
(aux must_check_ty env2 e4 g)
end
| FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____1012) -> begin
(((FStar_Pervasives_Native.fst t2)), (true), (g))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1071) -> begin
(

let uu____1092 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____1161 uu____1162 -> (match (((uu____1161), (uu____1162))) with
| ((env3, bs1, must_check_ty1, g1), (a, imp)) -> begin
(

let uu____1249 = (match (must_check_ty1) with
| true -> begin
((a), (true), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____1262 -> begin
(mk_binder1 env3 a)
end)
in (match (uu____1249) with
| (tb, must_check_ty2, g_a) -> begin
(

let b = ((tb), (imp))
in (

let bs2 = (FStar_List.append bs1 ((b)::[]))
in (

let env4 = (FStar_TypeChecker_Env.push_binders env3 ((b)::[]))
in (

let uu____1313 = (FStar_TypeChecker_Rel.conj_guard g_a g1)
in ((env4), (bs2), (must_check_ty2), (uu____1313))))))
end))
end)) ((env2), ([]), (must_check_ty), (g))))
in (match (uu____1092) with
| (env3, bs1, must_check_ty1, g1) -> begin
(

let uu____1356 = (aux must_check_ty1 env3 body g1)
in (match (uu____1356) with
| (res, must_check_ty2, g2) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____1394 = (FStar_Options.ml_ish ())
in (match (uu____1394) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____1397 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Util.arrow bs1 c)
in ((

let uu____1403 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____1403) with
| true -> begin
(

let uu____1404 = (FStar_Range.string_of_range r)
in (

let uu____1405 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____1406 = (FStar_Util.string_of_bool must_check_ty2)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" uu____1404 uu____1405 uu____1406))))
end
| uu____1407 -> begin
()
end));
((FStar_Util.Inl (t2)), (must_check_ty2), (g2));
)))
end))
end))
end
| uu____1414 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true), (g))
end
| uu____1429 -> begin
(

let uu____1430 = (new_implicit_var "" r env2 FStar_Syntax_Util.ktype0)
in (match (uu____1430) with
| (t2, uu____1454, g') -> begin
(

let uu____1468 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((FStar_Util.Inl (t2)), (false), (uu____1468)))
end))
end)
end)))
in (

let uu____1473 = (aux false env1 e1 FStar_TypeChecker_Rel.trivial_guard)
in (match (uu____1473) with
| (t2, b, g) -> begin
(

let t3 = (match (t2) with
| FStar_Util.Inr (c) -> begin
(

let uu____1507 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____1507) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1508 -> begin
(

let uu____1509 = (

let uu____1514 = (

let uu____1515 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____1515))
in ((FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec), (uu____1514)))
in (FStar_Errors.raise_error uu____1509 rng))
end))
end
| FStar_Util.Inl (t3) -> begin
t3
end)
in ((univ_vars2), (t3), (b), (g)))
end))))))
end))
end
| uu____1519 -> begin
(

let uu____1520 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____1520) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false), (FStar_TypeChecker_Rel.trivial_guard))
end))
end)))
end))


let pat_as_exp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p tc_annot -> (

let check_bv = (fun env1 x -> (

let uu____1616 = (

let uu____1621 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in (match (uu____1621) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____1626; FStar_Syntax_Syntax.vars = uu____1627} -> begin
(

let uu____1630 = (FStar_Syntax_Util.type_u ())
in (match (uu____1630) with
| (t, uu____1640) -> begin
(

let uu____1641 = (

let uu____1654 = (FStar_Syntax_Syntax.range_of_bv x)
in (new_implicit_var "" uu____1654 env1 t))
in (match (uu____1641) with
| (t1, uu____1660, g) -> begin
((t1), (g))
end))
end))
end
| t -> begin
(tc_annot env1 t)
end))
in (match (uu____1616) with
| (t_x, guard) -> begin
(((

let uu___103_1682 = x
in {FStar_Syntax_Syntax.ppname = uu___103_1682.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___103_1682.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (guard))
end)))
in (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = (match (c) with
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(FStar_ToSyntax_ToSyntax.desugar_machine_integer env1.FStar_TypeChecker_Env.dsenv repr sw p1.FStar_Syntax_Syntax.p)
end
| uu____1757 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
end)
in (([]), ([]), ([]), (env1), (e), (FStar_TypeChecker_Rel.trivial_guard), (p1)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____1765) -> begin
(

let uu____1770 = (FStar_Syntax_Util.type_u ())
in (match (uu____1770) with
| (k, uu____1796) -> begin
(

let uu____1797 = (

let uu____1810 = (FStar_Syntax_Syntax.range_of_bv x)
in (new_implicit_var "" uu____1810 env1 k))
in (match (uu____1797) with
| (t, uu____1832, g) -> begin
(

let x1 = (

let uu___104_1847 = x
in {FStar_Syntax_Syntax.ppname = uu___104_1847.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_1847.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____1848 = (

let uu____1861 = (FStar_Syntax_Syntax.range_of_bv x1)
in (new_implicit_var "" uu____1861 env1 t))
in (match (uu____1848) with
| (e, uu____1883, g') -> begin
(

let p2 = (

let uu___105_1900 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.p = uu___105_1900.FStar_Syntax_Syntax.p})
in (

let uu____1903 = (FStar_TypeChecker_Rel.conj_guard g g')
in (([]), ([]), ([]), (env1), (e), (uu____1903), (p2))))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____1911 = (check_bv env1 x)
in (match (uu____1911) with
| (x1, g) -> begin
(

let env2 = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env1 x1)
end
| uu____1939 -> begin
env1
end)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (g), (p1))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____1950 = (check_bv env1 x)
in (match (uu____1950) with
| (x1, g) -> begin
(

let env2 = (FStar_TypeChecker_Env.push_bv env1 x1)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ((x1)::[]), ([]), (env2), (e), (g), (p1))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2005 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____2151 uu____2152 -> (match (((uu____2151), (uu____2152))) with
| ((b, a, w, env2, args, guard, pats1), (p2, imp)) -> begin
(

let uu____2350 = (pat_as_arg_with_env allow_wc_dependence env2 p2)
in (match (uu____2350) with
| (b', a', w', env3, te, guard', pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____2425 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (

let uu____2426 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), (uu____2426), ((((pat), (imp)))::pats1))))
end))
end)) (([]), ([]), ([]), (env1), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([]))))
in (match (uu____2005) with
| (b, a, w, env2, args, guard, pats1) -> begin
(

let e = (

let uu____2569 = (

let uu____2574 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____2575 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____2574 uu____2575)))
in (uu____2569 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in (

let uu____2592 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____2603 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____2614 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____2592), (uu____2603), (uu____2614), (env2), (e), (guard), ((

let uu___106_2632 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___106_2632.FStar_Syntax_Syntax.p})))))))
end))
end))
in (

let rec elaborate_pat = (fun env1 p1 -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) r)
end
| uu____2684 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) r)
end))
in (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____2730 -> (match (uu____2730) with
| (p2, imp) -> begin
(

let uu____2749 = (elaborate_pat env1 p2)
in ((uu____2749), (imp)))
end)) pats)
in (

let uu____2754 = (FStar_TypeChecker_Env.lookup_datacon env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2754) with
| (uu____2761, t) -> begin
(

let uu____2763 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2763) with
| (f, uu____2779) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____2905)::uu____2906) -> begin
(

let uu____2949 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_TooManyPatternArguments), ("Too many pattern arguments")) uu____2949))
end
| ((uu____2958)::uu____2959, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____3037 -> (match (uu____3037) with
| (t1, imp) -> begin
(match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____3064 = (

let uu____3067 = (FStar_Syntax_Syntax.range_of_bv t1)
in FStar_Pervasives_Native.Some (uu____3067))
in (FStar_Syntax_Syntax.new_bv uu____3064 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____3069 = (maybe_dot inaccessible a r)
in ((uu____3069), (true)))))
end
| uu____3074 -> begin
(

let uu____3077 = (

let uu____3082 = (

let uu____3083 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____3083))
in ((FStar_Errors.Fatal_InsufficientPatternArguments), (uu____3082)))
in (

let uu____3084 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error uu____3077 uu____3084)))
end)
end))))
end
| ((f1)::formals', ((p2, p_imp))::pats') -> begin
(match (f1) with
| (uu____3158, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____3159))) when p_imp -> begin
(

let uu____3162 = (aux formals' pats')
in (((p2), (true)))::uu____3162)
end
| (uu____3179, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p2.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p3 = (

let uu____3187 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (maybe_dot inaccessible a uu____3187))
in (

let uu____3188 = (aux formals' pats2)
in (((p3), (true)))::uu____3188)))
end
| (uu____3205, imp) -> begin
(

let uu____3211 = (

let uu____3218 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p2), (uu____3218)))
in (

let uu____3221 = (aux formals' pats')
in (uu____3211)::uu____3221))
end)
end))
in (

let uu___107_3236 = p1
in (

let uu____3239 = (

let uu____3240 = (

let uu____3253 = (aux f pats1)
in ((fv), (uu____3253)))
in FStar_Syntax_Syntax.Pat_cons (uu____3240))
in {FStar_Syntax_Syntax.v = uu____3239; FStar_Syntax_Syntax.p = uu___107_3236.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____3270 -> begin
p1
end)))
in (

let one_pat = (fun allow_wc_dependence env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____3312 = (pat_as_arg_with_env allow_wc_dependence env1 p2)
in (match (uu____3312) with
| (b, a, w, env2, arg, guard, p3) -> begin
(

let uu____3370 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____3370) with
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____3396 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in (FStar_Errors.raise_error uu____3396 p3.FStar_Syntax_Syntax.p))
end
| uu____3419 -> begin
((b), (a), (w), (arg), (guard), (p3))
end))
end))))
in (

let uu____3428 = (one_pat true env p)
in (match (uu____3428) with
| (b, uu____3458, uu____3459, tm, guard, p1) -> begin
((b), (tm), (guard), (p1))
end)))))))


let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.pat = (fun env p exp -> (

let qq = p
in (

let rec aux = (fun p1 e -> (

let pkg = (fun q -> (FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p))
in (

let e1 = (FStar_Syntax_Util.unmeta e)
in (match (((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n))) with
| (uu____3521, FStar_Syntax_Syntax.Tm_uinst (e2, uu____3523)) -> begin
(aux p1 e2)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____3528), uu____3529) -> begin
(pkg p1.FStar_Syntax_Syntax.v)
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____3533 = (

let uu____3534 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3535 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____3534 uu____3535)))
in (failwith uu____3533))
end
| uu____3536 -> begin
()
end);
(

let uu____3538 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____3538) with
| true -> begin
(

let uu____3539 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3540 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____3539 uu____3540)))
end
| uu____3541 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___108_3544 = x
in {FStar_Syntax_Syntax.ppname = uu___108_3544.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___108_3544.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____3548 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____3548) with
| true -> begin
(

let uu____3549 = (

let uu____3550 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3551 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____3550 uu____3551)))
in (failwith uu____3549))
end
| uu____3552 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___109_3555 = x
in {FStar_Syntax_Syntax.ppname = uu___109_3555.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___109_3555.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____3557), uu____3558) -> begin
(pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e1)))))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____3582 = (

let uu____3583 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____3583)))
in (match (uu____3582) with
| true -> begin
(

let uu____3584 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3584))
end
| uu____3585 -> begin
()
end));
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____3603; FStar_Syntax_Syntax.vars = uu____3604}, args)) -> begin
((

let uu____3643 = (

let uu____3644 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____3644 Prims.op_Negation))
in (match (uu____3643) with
| true -> begin
(

let uu____3645 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3645))
end
| uu____3646 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____3787))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3862)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3899) -> begin
(

let pat = (

let uu____3921 = (aux argpat e2)
in (

let uu____3922 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3921), (uu____3922))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3927 -> begin
(

let uu____3950 = (

let uu____3951 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3952 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3951 uu____3952)))
in (failwith uu____3950))
end))
in (match_args [] args argpats)));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____3964; FStar_Syntax_Syntax.vars = uu____3965}, uu____3966); FStar_Syntax_Syntax.pos = uu____3967; FStar_Syntax_Syntax.vars = uu____3968}, args)) -> begin
((

let uu____4011 = (

let uu____4012 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____4012 Prims.op_Negation))
in (match (uu____4011) with
| true -> begin
(

let uu____4013 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____4013))
end
| uu____4014 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____4155))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____4230)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____4267) -> begin
(

let pat = (

let uu____4289 = (aux argpat e2)
in (

let uu____4290 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____4289), (uu____4290))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____4295 -> begin
(

let uu____4318 = (

let uu____4319 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____4320 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____4319 uu____4320)))
in (failwith uu____4318))
end))
in (match_args [] args argpats)));
)
end
| uu____4329 -> begin
(

let uu____4334 = (

let uu____4335 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____4336 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____4337 = (FStar_Syntax_Print.term_to_string exp)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____4335 uu____4336 uu____4337))))
in (failwith uu____4334))
end))))
in (aux p exp))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____4380 -> (match (uu____4380) with
| (p, i) -> begin
(

let uu____4397 = (decorated_pattern_as_term p)
in (match (uu____4397) with
| (vars, te) -> begin
(

let uu____4420 = (

let uu____4425 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____4425)))
in ((vars), (uu____4420)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4439 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____4439)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____4443 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____4443)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____4447 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____4447)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4468 = (

let uu____4485 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____4485 FStar_List.unzip))
in (match (uu____4468) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____4599 = (

let uu____4600 = (

let uu____4601 = (

let uu____4616 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____4616), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____4601))
in (mk1 uu____4600))
in ((vars1), (uu____4599))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let comp_univ_opt : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____4652, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.GTotal (uu____4662, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::uu____4676 -> begin
FStar_Pervasives_Native.Some (hd1)
end)
end))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____4698))::[] -> begin
wp
end
| uu____4715 -> begin
(

let uu____4724 = (

let uu____4725 = (

let uu____4726 = (FStar_List.map (fun uu____4736 -> (match (uu____4736) with
| (x, uu____4742) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____4726 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____4725))
in (failwith uu____4724))
end)
in (

let uu____4745 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____4745), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____4761 = (destruct_comp c)
in (match (uu____4761) with
| (u, uu____4769, wp) -> begin
(

let uu____4771 = (

let uu____4780 = (

let uu____4787 = (lift.FStar_TypeChecker_Env.mlift_wp u c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____4787))
in (uu____4780)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____4771; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____4815 = (

let uu____4822 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____4823 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____4822 uu____4823)))
in (match (uu____4815) with
| (m, uu____4825, uu____4826) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____4842 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____4842) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____4843 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____4885 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____4885) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____4922 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____4922) with
| (a, kwp) -> begin
(

let uu____4953 = (destruct_comp m1)
in (

let uu____4960 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____4953), (uu____4960))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags1 -> (

let uu____5040 = (

let uu____5041 = (

let uu____5050 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5050)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____5041; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp uu____5040)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags1 -> (

let uu____5122 = (FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)
in (match (uu____5122) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____5123 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1)
end)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu____5134 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____5134 lc.FStar_Syntax_Syntax.cflags (fun uu____5137 -> (

let uu____5138 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Subst.subst_comp subst1 uu____5138))))))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5144 = (

let uu____5145 = (FStar_Syntax_Subst.compress t)
in uu____5145.FStar_Syntax_Syntax.n)
in (match (uu____5144) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5148) -> begin
true
end
| uu____5161 -> begin
false
end)))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (reason1) -> begin
(

let uu____5218 = (

let uu____5219 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____5219))
in (match (uu____5218) with
| true -> begin
f
end
| uu____5220 -> begin
(

let uu____5221 = (reason1 ())
in (label uu____5221 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___110_5238 = g
in (

let uu____5239 = (

let uu____5240 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____5240))
in {FStar_TypeChecker_Env.guard_f = uu____5239; FStar_TypeChecker_Env.deferred = uu___110_5238.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___110_5238.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___110_5238.FStar_TypeChecker_Env.implicits}))
end))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____5260 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____5260) with
| true -> begin
c
end
| uu____5261 -> begin
(

let uu____5262 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5262) with
| true -> begin
c
end
| uu____5263 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____5321 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5321)::[])
in (

let us = (

let uu____5337 = (

let uu____5340 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____5340)::[])
in (u_res)::uu____5337)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____5346 = (

let uu____5351 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____5352 = (

let uu____5353 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5360 = (

let uu____5369 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____5376 = (

let uu____5385 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____5385)::[])
in (uu____5369)::uu____5376))
in (uu____5353)::uu____5360))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5351 uu____5352)))
in (uu____5346 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____5419 = (destruct_comp c1)
in (match (uu____5419) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end)))


let close_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____5454 -> (

let uu____5455 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (close_comp env bvs uu____5455)))))


let should_not_inline_lc : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___80_5464 -> (match (uu___80_5464) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____5465 -> begin
false
end)))))


let should_return : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun env eopt lc -> (match (eopt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (e) -> begin
((((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) && (

let uu____5487 = (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____5487)))) && (

let uu____5494 = (FStar_Syntax_Util.head_and_args' e)
in (match (uu____5494) with
| (head1, uu____5508) -> begin
(

let uu____5525 = (

let uu____5526 = (FStar_Syntax_Util.un_uinst head1)
in uu____5526.FStar_Syntax_Syntax.n)
in (match (uu____5525) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5530 = (

let uu____5531 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_irreducible env uu____5531))
in (not (uu____5530)))
end
| uu____5532 -> begin
true
end))
end))) && (

let uu____5534 = (should_not_inline_lc lc)
in (not (uu____5534))))
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp = (fun env u_t_opt t v1 -> (

let c = (

let uu____5568 = (

let uu____5569 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____5569))
in (match (uu____5568) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____5570 -> begin
(

let uu____5571 = (FStar_Syntax_Util.is_unit t)
in (match (uu____5571) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero)))
end
| uu____5572 -> begin
(

let m = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let u_t = (match (u_t_opt) with
| FStar_Pervasives_Native.None -> begin
(env.FStar_TypeChecker_Env.universe_of env t)
end
| FStar_Pervasives_Native.Some (u_t) -> begin
u_t
end)
in (

let wp = (

let uu____5577 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5577) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____5578 -> begin
(

let uu____5579 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____5579) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____5589 = (

let uu____5590 = (

let uu____5595 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____5596 = (

let uu____5597 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____5604 = (

let uu____5613 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____5613)::[])
in (uu____5597)::uu____5604))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5595 uu____5596)))
in (uu____5590 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env uu____5589)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
end))
in ((

let uu____5641 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____5641) with
| true -> begin
(

let uu____5642 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____5643 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____5644 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____5642 uu____5643 uu____5644))))
end
| uu____5645 -> begin
()
end));
c;
)))


let weaken_flags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags1 -> (

let uu____5657 = (FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___81_5661 -> (match (uu___81_5661) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____5662 -> begin
false
end))))
in (match (uu____5657) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____5665 -> begin
(FStar_All.pipe_right flags1 (FStar_List.collect (fun uu___82_5671 -> (match (uu___82_5671) with
| FStar_Syntax_Syntax.TOTAL -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]
end
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]
end
| f -> begin
(f)::[]
end))))
end)))


let weaken_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env c formula -> (

let uu____5690 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____5690) with
| true -> begin
c
end
| uu____5691 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____5693 = (destruct_comp c1)
in (match (uu____5693) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5707 = (

let uu____5712 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____5713 = (

let uu____5714 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5721 = (

let uu____5730 = (FStar_Syntax_Syntax.as_arg formula)
in (

let uu____5737 = (

let uu____5746 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5746)::[])
in (uu____5730)::uu____5737))
in (uu____5714)::uu____5721))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5712 uu____5713)))
in (uu____5707 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (

let uu____5779 = (weaken_flags c1.FStar_Syntax_Syntax.flags)
in (mk_comp md u_res_t res_t wp1 uu____5779))))
end)))
end)))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____5802 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let uu____5804 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5804) with
| true -> begin
c
end
| uu____5805 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(weaken_comp env c f1)
end)
end))))
in (

let uu____5807 = (weaken_flags lc.FStar_Syntax_Syntax.cflags)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ uu____5807 weaken))))


let strengthen_comp : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun env reason c f flags1 -> (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____5848 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____5850 = (destruct_comp c1)
in (match (uu____5850) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5864 = (

let uu____5869 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____5870 = (

let uu____5871 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5878 = (

let uu____5887 = (

let uu____5894 = (

let uu____5895 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____5895 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5894))
in (

let uu____5902 = (

let uu____5911 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5911)::[])
in (uu____5887)::uu____5902))
in (uu____5871)::uu____5878))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5869 uu____5870)))
in (uu____5864 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 flags1)))
end)))
end))


let strengthen_precondition : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e_for_debug_only lc g0 -> (

let uu____5986 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____5986) with
| true -> begin
((lc), (g0))
end
| uu____5991 -> begin
(

let flags1 = (

let uu____5995 = (

let uu____6002 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____6002) with
| true -> begin
((true), ((FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]))
end
| uu____6011 -> begin
((false), ([]))
end))
in (match (uu____5995) with
| (maybe_trivial_post, flags1) -> begin
(

let uu____6022 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___83_6030 -> (match (uu___83_6030) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.SOMETRIVIAL when (not (maybe_trivial_post)) -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION when (not (maybe_trivial_post)) -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]
end
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____6033 -> begin
[]
end))))
in (FStar_List.append flags1 uu____6022))
end))
in (

let strengthen = (fun uu____6039 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____6041 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____6043 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____6043) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____6046 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6046) with
| true -> begin
(

let uu____6047 = (FStar_TypeChecker_Normalize.term_to_string env e_for_debug_only)
in (

let uu____6048 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____6047 uu____6048)))
end
| uu____6049 -> begin
()
end));
(strengthen_comp env reason c f flags1);
)
end)))
end)))
in (

let uu____6050 = (

let uu____6051 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____6051 lc.FStar_Syntax_Syntax.res_typ flags1 strengthen))
in ((uu____6050), ((

let uu___111_6053 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___111_6053.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___111_6053.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___111_6053.FStar_TypeChecker_Env.implicits}))))))
end)))


let lcomp_has_trivial_postcondition : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) || (FStar_Util.for_some (fun uu___84_6060 -> (match (uu___84_6060) with
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
true
end
| uu____6061 -> begin
false
end)) lc.FStar_Syntax_Syntax.cflags)))


let maybe_add_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env uopt lc e -> (

let uu____6088 = ((FStar_Syntax_Util.is_lcomp_partial_return lc) || env.FStar_TypeChecker_Env.lax)
in (match (uu____6088) with
| true -> begin
e
end
| uu____6091 -> begin
(

let uu____6092 = ((lcomp_has_trivial_postcondition lc) && (

let uu____6094 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____6094)))
in (match (uu____6092) with
| true -> begin
(

let u = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
u
end
| FStar_Pervasives_Native.None -> begin
(env.FStar_TypeChecker_Env.universe_of env lc.FStar_Syntax_Syntax.res_typ)
end)
in (FStar_Syntax_Util.mk_with_type u lc.FStar_Syntax_Syntax.res_typ e))
end
| uu____6117 -> begin
e
end))
end)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____6144 -> (match (uu____6144) with
| (b, lc2) -> begin
(

let debug1 = (fun f -> (

let uu____6164 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____6164) with
| true -> begin
(f ())
end
| uu____6165 -> begin
()
end)))
in (

let lc11 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc21 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc11 lc21)
in (

let bind_flags = (

let uu____6172 = ((should_not_inline_lc lc11) || (should_not_inline_lc lc21))
in (match (uu____6172) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____6175 -> begin
(

let flags1 = (

let uu____6179 = (FStar_Syntax_Util.is_total_lcomp lc11)
in (match (uu____6179) with
| true -> begin
(

let uu____6182 = (FStar_Syntax_Util.is_total_lcomp lc21)
in (match (uu____6182) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____6185 -> begin
(

let uu____6186 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
in (match (uu____6186) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____6189 -> begin
[]
end))
end))
end
| uu____6190 -> begin
(

let uu____6191 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) && (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21))
in (match (uu____6191) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____6194 -> begin
[]
end))
end))
in (

let uu____6195 = (lcomp_has_trivial_postcondition lc21)
in (match (uu____6195) with
| true -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::flags1
end
| uu____6198 -> begin
flags1
end)))
end))
in (

let bind_it = (fun uu____6204 -> (

let uu____6205 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____6205) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____6207 -> begin
(

let c1 = (FStar_Syntax_Syntax.lcomp_comp lc11)
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp lc21)
in ((debug1 (fun uu____6219 -> (

let uu____6220 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____6221 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____6223 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n" uu____6220 uu____6221 uu____6223))))));
(

let aux = (fun uu____6237 -> (

let uu____6238 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____6238) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____6259) -> begin
(

let uu____6260 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____6260) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____6273 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____6278 -> begin
(

let uu____6279 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____6279) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____6292 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun e1opt1 reason -> (match (((e1opt1), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____6350 = (

let uu____6355 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____6355), (reason)))
in FStar_Util.Inl (uu____6350))
end
| uu____6362 -> begin
(aux ())
end))
in (

let try_simplify = (fun uu____6386 -> (

let rec maybe_close = (fun t x c -> (

let uu____6403 = (

let uu____6404 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in uu____6404.FStar_Syntax_Syntax.n)
in (match (uu____6403) with
| FStar_Syntax_Syntax.Tm_refine (y, uu____6408) -> begin
(maybe_close y.FStar_Syntax_Syntax.sort x c)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____6414 -> begin
c
end)))
in (

let uu____6415 = (

let uu____6416 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____6416))
in (match (uu____6415) with
| true -> begin
(

let uu____6427 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____6427) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____6440 -> begin
(

let uu____6441 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonTrivialPreConditionInPrims), ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")) uu____6441))
end))
end
| uu____6450 -> begin
(

let uu____6451 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____6451) with
| true -> begin
(subst_c2 e1opt "both total")
end
| uu____6460 -> begin
(

let uu____6461 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____6461) with
| true -> begin
(

let uu____6470 = (

let uu____6475 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____6475), ("both gtot")))
in FStar_Util.Inl (uu____6470))
end
| uu____6480 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____6507 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____6509 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____6509))))
in (match (uu____6507) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___112_6522 = x
in {FStar_Syntax_Syntax.ppname = uu___112_6522.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_6522.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____6523 = (

let uu____6528 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____6528), ("c1 Tot")))
in FStar_Util.Inl (uu____6523))))
end
| uu____6533 -> begin
(aux ())
end))
end
| uu____6534 -> begin
(aux ())
end)
end))
end))
end))))
in (

let uu____6545 = (try_simplify ())
in (match (uu____6545) with
| FStar_Util.Inl (c, reason) -> begin
((debug1 (fun uu____6565 -> (

let uu____6566 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "(2) bind: Simplified (because %s) to\n\t%s\n" reason uu____6566))));
c;
)
end
| FStar_Util.Inr (reason) -> begin
((debug1 (fun uu____6575 -> (FStar_Util.print1 "(2) bind: Not simplified because %s\n" reason)));
(

let mk_bind = (fun c11 b1 c21 -> (

let uu____6596 = (lift_and_destruct env c11 c21)
in (match (uu____6596) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b1) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6649 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____6649)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____6651 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6651)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____6678 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____6685 = (

let uu____6694 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____6701 = (

let uu____6710 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____6717 = (

let uu____6726 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____6733 = (

let uu____6742 = (

let uu____6749 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____6749))
in (uu____6742)::[])
in (uu____6726)::uu____6733))
in (uu____6710)::uu____6717))
in (uu____6694)::uu____6701))
in (uu____6678)::uu____6685))
in (

let wp = (

let uu____6789 = (

let uu____6794 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6794 wp_args))
in (uu____6789 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (mk_comp md u_t2 t2 wp bind_flags))))))
end)))
in (

let mk_seq = (fun c11 b1 c21 -> (

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in (

let uu____6819 = (FStar_TypeChecker_Env.join env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____6819) with
| (m, uu____6827, lift2) -> begin
(

let c23 = (

let uu____6830 = (lift_comp c22 m lift2)
in (FStar_Syntax_Syntax.mk_Comp uu____6830))
in (

let uu____6831 = (destruct_comp c12)
in (match (uu____6831) with
| (u1, t1, wp1) -> begin
(

let md_pure_or_ghost = (FStar_TypeChecker_Env.get_effect_decl env c12.FStar_Syntax_Syntax.effect_name)
in (

let vc1 = (

let uu____6845 = (

let uu____6850 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u1)::[]) env md_pure_or_ghost md_pure_or_ghost.FStar_Syntax_Syntax.trivial)
in (

let uu____6851 = (

let uu____6852 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____6859 = (

let uu____6868 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____6868)::[])
in (uu____6852)::uu____6859))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6850 uu____6851)))
in (uu____6845 FStar_Pervasives_Native.None r1))
in (strengthen_comp env FStar_Pervasives_Native.None c23 vc1 bind_flags)))
end)))
end)))))
in (

let c1_typ = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____6899 = (destruct_comp c1_typ)
in (match (uu____6899) with
| (u_res_t1, res_t1, uu____6908) -> begin
(

let uu____6909 = ((FStar_Option.isSome b) && (should_return env e1opt lc11))
in (match (uu____6909) with
| true -> begin
(

let e1 = (FStar_Option.get e1opt)
in (

let x = (FStar_Option.get b)
in (

let uu____6912 = (FStar_Syntax_Util.is_partial_return c1)
in (match (uu____6912) with
| true -> begin
((debug1 (fun uu____6920 -> (

let uu____6921 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____6922 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case a): Substituting %s for %s" uu____6921 uu____6922)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (mk_bind c1 b c21));
)
end
| uu____6926 -> begin
(

let uu____6927 = (((FStar_Options.vcgen_optimize_bind_as_seq ()) && (lcomp_has_trivial_postcondition lc11)) && (

let uu____6929 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____6929)))
in (match (uu____6927) with
| true -> begin
(

let e1' = (

let uu____6949 = (FStar_Options.vcgen_decorate_with_type ())
in (match (uu____6949) with
| true -> begin
(FStar_Syntax_Util.mk_with_type u_res_t1 res_t1 e1)
end
| uu____6950 -> begin
e1
end))
in ((debug1 (fun uu____6958 -> (

let uu____6959 = (FStar_TypeChecker_Normalize.term_to_string env e1')
in (

let uu____6960 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case b): Substituting %s for %s" uu____6959 uu____6960)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1'))))::[]) c2)
in (mk_seq c1 b c21));
))
end
| uu____6964 -> begin
((debug1 (fun uu____6972 -> (

let uu____6973 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____6974 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case c): Adding equality %s = %s" uu____6973 uu____6974)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (

let x_eq_e = (

let uu____6979 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq2 u_res_t1 res_t1 e1 uu____6979))
in (

let c22 = (weaken_comp env c21 x_eq_e)
in (mk_bind c1 b c22))));
)
end))
end))))
end
| uu____6981 -> begin
(mk_bind c1 b c2)
end))
end)))));
)
end)))));
)))
end)))
in (FStar_Syntax_Syntax.mk_lcomp joined_eff lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it)))))))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____6995 -> begin
g2
end))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let should_return1 = ((((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)) && (should_return env (FStar_Pervasives_Native.Some (e)) lc)) && (

let uu____7017 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____7017))))
in (

let flags1 = (match (should_return1) with
| true -> begin
(

let uu____7023 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____7023) with
| true -> begin
(FStar_Syntax_Syntax.RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____7026 -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end))
end
| uu____7027 -> begin
lc.FStar_Syntax_Syntax.cflags
end)
in (

let refine1 = (fun uu____7033 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let u_t = (match ((comp_univ_opt c)) with
| FStar_Pervasives_Native.Some (u_t) -> begin
u_t
end
| FStar_Pervasives_Native.None -> begin
(env.FStar_TypeChecker_Env.universe_of env (FStar_Syntax_Util.comp_result c))
end)
in (

let uu____7037 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____7037) with
| true -> begin
(

let retc = (return_value env (FStar_Pervasives_Native.Some (u_t)) (FStar_Syntax_Util.comp_result c) e)
in (

let uu____7039 = (

let uu____7040 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____7040)))
in (match (uu____7039) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___113_7043 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___113_7043.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___113_7043.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___113_7043.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____7044 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags1)
end)))
end
| uu____7045 -> begin
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

let uu____7054 = (

let uu____7055 = (return_value env (FStar_Pervasives_Native.Some (u_t)) t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____7055 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____7054))
in (

let eq1 = (FStar_Syntax_Util.mk_eq2 u_t t xexp e)
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____7058 = (

let uu____7059 = (

let uu____7060 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None uu____7060 ((FStar_Pervasives_Native.Some (x)), (eq_ret))))
in (FStar_Syntax_Syntax.lcomp_comp uu____7059))
in (FStar_Syntax_Util.comp_set_flags uu____7058 flags1))))))))))
end)))))
in (match ((not (should_return1))) with
| true -> begin
lc
end
| uu____7063 -> begin
(FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ flags1 refine1)
end)))))


let maybe_return_e2_and_bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r env e1opt lc1 e2 uu____7095 -> (match (uu____7095) with
| (x, lc2) -> begin
(

let lc21 = (

let eff1 = (FStar_TypeChecker_Env.norm_eff_name env lc1.FStar_Syntax_Syntax.eff_name)
in (

let eff2 = (FStar_TypeChecker_Env.norm_eff_name env lc2.FStar_Syntax_Syntax.eff_name)
in (

let uu____7107 = (((

let uu____7110 = (is_pure_or_ghost_effect env eff1)
in (not (uu____7110))) || (should_not_inline_lc lc1)) && (is_pure_or_ghost_effect env eff2))
in (match (uu____7107) with
| true -> begin
(maybe_assume_result_eq_pure_term env e2 lc2)
end
| uu____7111 -> begin
lc2
end))))
in (bind r env e1opt lc1 ((x), (lc21))))
end))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____7124 = (

let uu____7125 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____7125))
in (FStar_Syntax_Syntax.fvar uu____7124 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp)) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____7191 -> (match (uu____7191) with
| (uu____7204, eff_label, uu____7206, uu____7207) -> begin
(join_effects env eff eff_label)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let uu____7218 = (

let uu____7225 = (FStar_All.pipe_right lcases (FStar_Util.for_some (fun uu____7259 -> (match (uu____7259) with
| (uu____7272, uu____7273, flags1, uu____7275) -> begin
(FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___85_7289 -> (match (uu___85_7289) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____7290 -> begin
false
end))))
end))))
in (match (uu____7225) with
| true -> begin
((true), ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
end
| uu____7299 -> begin
((false), ([]))
end))
in (match (uu____7218) with
| (should_not_inline_whole_match, bind_cases_flags) -> begin
(

let bind_cases = (fun uu____7313 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____7315 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____7315) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____7316 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____7349 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____7350 = (

let uu____7355 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____7356 = (

let uu____7357 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____7364 = (

let uu____7373 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____7380 = (

let uu____7389 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____7396 = (

let uu____7405 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____7405)::[])
in (uu____7389)::uu____7396))
in (uu____7373)::uu____7380))
in (uu____7357)::uu____7364))
in (FStar_Syntax_Syntax.mk_Tm_app uu____7355 uu____7356)))
in (uu____7350 FStar_Pervasives_Native.None uu____7349))))
in (

let default_case = (

let post_k = (

let uu____7448 = (

let uu____7455 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____7455)::[])
in (

let uu____7468 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____7448 uu____7468)))
in (

let kwp = (

let uu____7474 = (

let uu____7481 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____7481)::[])
in (

let uu____7494 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____7474 uu____7494)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____7501 = (

let uu____7502 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____7502)::[])
in (

let uu____7515 = (

let uu____7518 = (

let uu____7525 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____7525))
in (

let uu____7526 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____7518 uu____7526)))
in (FStar_Syntax_Util.abs uu____7501 uu____7515 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let maybe_return = (fun eff_label_then cthen -> (

let uu____7548 = (should_not_inline_whole_match || (

let uu____7550 = (is_pure_or_ghost_effect env eff)
in (not (uu____7550))))
in (match (uu____7548) with
| true -> begin
(cthen true)
end
| uu____7551 -> begin
(cthen false)
end)))
in (

let comp = (FStar_List.fold_right (fun uu____7583 celse -> (match (uu____7583) with
| (g, eff_label, uu____7599, cthen) -> begin
(

let uu____7611 = (

let uu____7636 = (

let uu____7637 = (maybe_return eff_label cthen)
in (FStar_Syntax_Syntax.lcomp_comp uu____7637))
in (lift_and_destruct env uu____7636 celse))
in (match (uu____7611) with
| ((md, uu____7639, uu____7640), (uu____7641, uu____7642, wp_then), (uu____7644, uu____7645, wp_else)) -> begin
(

let uu____7665 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____7665 []))
end))
end)) lcases default_case)
in (match (lcases) with
| [] -> begin
comp
end
| (uu____7679)::[] -> begin
comp
end
| uu____7719 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____7737 = (destruct_comp comp1)
in (match (uu____7737) with
| (uu____7744, uu____7745, wp) -> begin
(

let wp1 = (

let uu____7750 = (

let uu____7755 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____7756 = (

let uu____7757 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____7764 = (

let uu____7773 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____7773)::[])
in (uu____7757)::uu____7764))
in (FStar_Syntax_Syntax.mk_Tm_app uu____7755 uu____7756)))
in (uu____7750 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 bind_cases_flags))
end))))
end)))))
end))))
in (FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags bind_cases))
end))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____7832 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____7832) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7841 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____7846 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____7841 uu____7846)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____7889 = (

let uu____7890 = (FStar_Syntax_Subst.compress t2)
in uu____7890.FStar_Syntax_Syntax.n)
in (match (uu____7889) with
| FStar_Syntax_Syntax.Tm_type (uu____7893) -> begin
true
end
| uu____7894 -> begin
false
end))))
in (

let uu____7895 = (

let uu____7896 = (FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ)
in uu____7896.FStar_Syntax_Syntax.n)
in (match (uu____7895) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____7904 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (

let uu____7914 = (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____7914 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let lc1 = (

let uu____7916 = (

let uu____7917 = (

let uu____7918 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____7918))
in ((FStar_Pervasives_Native.None), (uu____7917)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____7916))
in (

let e1 = (

let uu____7924 = (

let uu____7929 = (

let uu____7930 = (FStar_Syntax_Syntax.as_arg e)
in (uu____7930)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7929))
in (uu____7924 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____7951 -> begin
((e), (lc))
end))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____7988 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____7988) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____8011 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____8033 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____8033), (false)))
end
| uu____8038 -> begin
(

let uu____8039 = (FStar_TypeChecker_Rel.get_subtyping_predicate env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____8039), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____8050) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____8059 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Errors.raise_error uu____8059 e.FStar_Syntax_Syntax.pos))
end
| uu____8070 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___114_8073 = lc
in {FStar_Syntax_Syntax.eff_name = uu___114_8073.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___114_8073.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___114_8073.FStar_Syntax_Syntax.comp_thunk})), (FStar_TypeChecker_Rel.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____8078 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____8078) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___115_8086 = lc
in {FStar_Syntax_Syntax.eff_name = uu___115_8086.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___115_8086.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___115_8086.FStar_Syntax_Syntax.comp_thunk})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___116_8089 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___116_8089.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___116_8089.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___116_8089.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____8095 -> (

let uu____8096 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____8096) with
| true -> begin
(FStar_Syntax_Syntax.lcomp_comp lc)
end
| uu____8097 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in (

let uu____8099 = (

let uu____8100 = (FStar_Syntax_Subst.compress f1)
in uu____8100.FStar_Syntax_Syntax.n)
in (match (uu____8099) with
| FStar_Syntax_Syntax.Tm_abs (uu____8103, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8105; FStar_Syntax_Syntax.vars = uu____8106}, uu____8107) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___117_8129 = lc
in {FStar_Syntax_Syntax.eff_name = uu___117_8129.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___117_8129.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___117_8129.FStar_Syntax_Syntax.comp_thunk})
in (FStar_Syntax_Syntax.lcomp_comp lc1))
end
| uu____8130 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((

let uu____8133 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____8133) with
| true -> begin
(

let uu____8134 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____8135 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____8136 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____8137 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____8134 uu____8135 uu____8136 uu____8137)))))
end
| uu____8138 -> begin
()
end));
(

let u_t_opt = (comp_univ_opt c)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let cret = (return_value env u_t_opt t xexp)
in (

let guard = (match (apply_guard1) with
| true -> begin
(

let uu____8146 = (

let uu____8151 = (

let uu____8152 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____8152)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____8151))
in (uu____8146 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____8173 -> begin
f1
end)
in (

let uu____8174 = (

let uu____8179 = (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____8196 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____8197 = (FStar_Syntax_Util.lcomp_of_comp cret)
in (

let uu____8198 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____8179 uu____8196 e uu____8197 uu____8198)))))
in (match (uu____8174) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___118_8202 = x
in {FStar_Syntax_Syntax.ppname = uu___118_8202.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_8202.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____8204 = (FStar_Syntax_Util.lcomp_of_comp c)
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____8204 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((

let uu____8209 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____8209) with
| true -> begin
(

let uu____8210 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____8210))
end
| uu____8211 -> begin
()
end));
c2;
))))
end)))))));
))
end)))
end)))
in (

let flags1 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___86_8220 -> (match (uu___86_8220) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____8223 -> begin
[]
end))))
in (

let lc1 = (

let uu____8225 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____8225 t flags1 strengthen))
in (

let g2 = (

let uu___119_8227 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___119_8227.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___119_8227.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___119_8227.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____8262 = (

let uu____8263 = (

let uu____8268 = (

let uu____8269 = (

let uu____8276 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____8276))
in (uu____8269)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____8268))
in (uu____8263 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____8262))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____8297 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____8297) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____8306 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____8313) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____8328) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____8344 = ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))
in (match (uu____8344) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____8358))::((ens, uu____8360))::uu____8361 -> begin
(

let uu____8390 = (

let uu____8393 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____8393))
in (

let uu____8394 = (

let uu____8395 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____8395))
in ((uu____8390), (uu____8394))))
end
| uu____8398 -> begin
(

let uu____8407 = (

let uu____8412 = (

let uu____8413 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____8413))
in ((FStar_Errors.Fatal_EffectConstructorNotFullyApplied), (uu____8412)))
in (FStar_Errors.raise_error uu____8407 comp.FStar_Syntax_Syntax.pos))
end)
end
| uu____8420 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____8429))::uu____8430 -> begin
(

let uu____8449 = (

let uu____8454 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8454))
in (match (uu____8449) with
| (us_r, uu____8486) -> begin
(

let uu____8487 = (

let uu____8492 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8492))
in (match (uu____8487) with
| (us_e, uu____8524) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____8527 = (

let uu____8528 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar uu____8528 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8527 us_r))
in (

let as_ens = (

let uu____8530 = (

let uu____8531 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar uu____8531 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8530 us_e))
in (

let req = (

let uu____8535 = (

let uu____8540 = (

let uu____8541 = (

let uu____8550 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____8550)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____8541)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____8540))
in (uu____8535 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____8584 = (

let uu____8589 = (

let uu____8590 = (

let uu____8599 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____8599)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____8590)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____8589))
in (uu____8584 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____8630 = (

let uu____8633 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____8633))
in (

let uu____8634 = (

let uu____8635 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____8635))
in ((uu____8630), (uu____8634)))))))))
end))
end))
end
| uu____8638 -> begin
(failwith "Impossible")
end))
end))
end)
end)))))


let reify_body : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let tm = (FStar_Syntax_Util.mk_reify t)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____8668 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____8668) with
| true -> begin
(

let uu____8669 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____8670 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____8669 uu____8670)))
end
| uu____8671 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____8714 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____8714) with
| true -> begin
(

let uu____8715 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____8716 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____8715 uu____8716)))
end
| uu____8717 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____8723 = (

let uu____8724 = (

let uu____8725 = (FStar_Syntax_Subst.compress t)
in uu____8725.FStar_Syntax_Syntax.n)
in (match (uu____8724) with
| FStar_Syntax_Syntax.Tm_app (uu____8728) -> begin
false
end
| uu____8743 -> begin
true
end))
in (match (uu____8723) with
| true -> begin
t
end
| uu____8744 -> begin
(

let uu____8745 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____8745) with
| (head1, args) -> begin
(

let uu____8782 = (

let uu____8783 = (

let uu____8784 = (FStar_Syntax_Subst.compress head1)
in uu____8784.FStar_Syntax_Syntax.n)
in (match (uu____8783) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____8787 -> begin
false
end))
in (match (uu____8782) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____8809 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____8818 -> begin
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
| uu____8847 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____8854 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____8854) with
| (formals, uu____8868) -> begin
(

let n_implicits = (

let uu____8886 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____8964 -> (match (uu____8964) with
| (uu____8971, imp) -> begin
((Prims.op_Equality imp FStar_Pervasives_Native.None) || (Prims.op_Equality imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality))))
end))))
in (match (uu____8886) with
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

let uu____9104 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____9104) with
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

let uu____9128 = (

let uu____9133 = (

let uu____9134 = (FStar_Util.string_of_int n_expected)
in (

let uu____9141 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____9142 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____9134 uu____9141 uu____9142))))
in ((FStar_Errors.Fatal_MissingImplicitArguments), (uu____9133)))
in (

let uu____9149 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____9128 uu____9149)))
end
| uu____9152 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___87_9172 -> (match (uu___87_9172) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____9202 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____9202) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_18), uu____9317) when (_0_18 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____9360, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____9393 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____9393) with
| (v1, uu____9433, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____9452 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____9452) with
| (args, bs3, subst3, g') -> begin
(

let uu____9545 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____9545)))
end)))
end)))
end
| (uu____9572, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____9618 = (

let uu____9645 = (inst_n_binders t)
in (aux [] uu____9645 bs1))
in (match (uu____9618) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____9716) -> begin
((e), (torig), (guard))
end
| (uu____9747, []) when (

let uu____9778 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____9778))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____9779 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____9807 -> begin
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
| uu____9820 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____9830 = (

let uu____9833 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____9833 (FStar_List.map (fun u -> (

let uu____9843 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____9843 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____9830 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____9864 = (FStar_Util.set_is_empty x)
in (match (uu____9864) with
| true -> begin
[]
end
| uu____9867 -> begin
(

let s = (

let uu____9871 = (

let uu____9874 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____9874))
in (FStar_All.pipe_right uu____9871 FStar_Util.set_elements))
in ((

let uu____9882 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9882) with
| true -> begin
(

let uu____9883 = (

let uu____9884 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____9884))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____9883))
end
| uu____9887 -> begin
()
end));
(

let r = (

let uu____9891 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____9891))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____9906 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9906) with
| true -> begin
(

let uu____9907 = (

let uu____9908 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____9908))
in (

let uu____9909 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____9910 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____9907 uu____9909 uu____9910))))
end
| uu____9911 -> begin
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

let uu____9936 = (FStar_Util.set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____9936 FStar_Util.set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____9974) -> begin
generalized_univ_names
end
| (uu____9981, []) -> begin
explicit_univ_names
end
| uu____9988 -> begin
(

let uu____9997 = (

let uu____10002 = (

let uu____10003 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____10003))
in ((FStar_Errors.Fatal_UnexpectedGeneralizedUniverse), (uu____10002)))
in (FStar_Errors.raise_error uu____9997 t.FStar_Syntax_Syntax.pos))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in ((

let uu____10021 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____10021) with
| true -> begin
(

let uu____10022 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____10023 = (FStar_Syntax_Print.univ_names_to_string univnames1)
in (FStar_Util.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" uu____10022 uu____10023)))
end
| uu____10024 -> begin
()
end));
(

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____10029 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____10029) with
| true -> begin
(

let uu____10030 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____10030))
end
| uu____10031 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____10036 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____10036) with
| true -> begin
(

let uu____10037 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____10038 = (FStar_Syntax_Print.univ_names_to_string gen1)
in (FStar_Util.print2 "After generalization, t: %s and univs: %s\n" uu____10037 uu____10038)))
end
| uu____10039 -> begin
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
));
))))


let gen : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list FStar_Pervasives_Native.option = (fun env is_rec lecs -> (

let uu____10116 = (

let uu____10117 = (FStar_Util.for_all (fun uu____10130 -> (match (uu____10130) with
| (uu____10139, uu____10140, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____10117))
in (match (uu____10116) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____10180 -> begin
(

let norm1 = (fun c -> ((

let uu____10188 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____10188) with
| true -> begin
(

let uu____10189 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____10189))
end
| uu____10190 -> begin
()
end));
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env c)
in ((

let uu____10193 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____10193) with
| true -> begin
(

let uu____10194 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10194))
end
| uu____10195 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____10209 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____10209 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____10245 -> (match (uu____10245) with
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

let uu____10289 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____10289) with
| true -> begin
(

let uu____10290 = (

let uu____10291 = (

let uu____10294 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____10294 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____10291 (FStar_String.concat ", ")))
in (

let uu____10337 = (

let uu____10338 = (

let uu____10341 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____10341 (FStar_List.map (fun u -> (

let uu____10352 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____10353 = (FStar_Syntax_Print.term_to_string u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____10352 uu____10353)))))))
in (FStar_All.pipe_right uu____10338 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10290 uu____10337)))
end
| uu____10356 -> begin
()
end));
(

let univs2 = (

let uu____10360 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uv -> (

let uu____10372 = (FStar_Syntax_Free.univs uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.set_union univs2 uu____10372))) univs1 uu____10360))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____10379 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____10379) with
| true -> begin
(

let uu____10380 = (

let uu____10381 = (

let uu____10384 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____10384 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____10381 (FStar_String.concat ", ")))
in (

let uu____10427 = (

let uu____10428 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> (

let uu____10439 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____10440 = (FStar_TypeChecker_Normalize.term_to_string env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____10439 uu____10440))))))
in (FStar_All.pipe_right uu____10428 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____10380 uu____10427)))
end
| uu____10443 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
))))))
end))
in (

let uu____10454 = (

let uu____10471 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____10471))
in (match (uu____10454) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____10563 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____10563) with
| true -> begin
()
end
| uu____10564 -> begin
(

let uu____10565 = lec_hd
in (match (uu____10565) with
| (lb1, uu____10573, uu____10574) -> begin
(

let uu____10575 = lec2
in (match (uu____10575) with
| (lb2, uu____10583, uu____10584) -> begin
(

let msg = (

let uu____10586 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____10587 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____10586 uu____10587)))
in (

let uu____10588 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleSetOfUniverse), (msg)) uu____10588)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun u -> (FStar_All.pipe_right u21 (FStar_Util.for_some (fun u' -> (FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head u'.FStar_Syntax_Syntax.ctx_uvar_head))))))))
in (

let uu____10652 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____10652) with
| true -> begin
()
end
| uu____10653 -> begin
(

let uu____10654 = lec_hd
in (match (uu____10654) with
| (lb1, uu____10662, uu____10663) -> begin
(

let uu____10664 = lec2
in (match (uu____10664) with
| (lb2, uu____10672, uu____10673) -> begin
(

let msg = (

let uu____10675 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____10676 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____10675 uu____10676)))
in (

let uu____10677 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleNumberOfTypes), (msg)) uu____10677)))
end))
end))
end))))
in (

let lecs1 = (

let uu____10687 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____10746 = (univs_and_uvars_of_lec this_lec)
in (match (uu____10746) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____10687 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail1 = (fun k -> (

let uu____10847 = lec_hd
in (match (uu____10847) with
| (lbname, e, c) -> begin
(

let uu____10857 = (

let uu____10862 = (

let uu____10863 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____10864 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____10865 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____10863 uu____10864 uu____10865))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____10862)))
in (

let uu____10866 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____10857 uu____10866)))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun u -> (

let uu____10887 = (FStar_Syntax_Unionfind.find u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____10887) with
| FStar_Pervasives_Native.Some (uu____10896) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____10903 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____10907 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____10907) with
| (bs, kres) -> begin
((

let uu____10945 = (

let uu____10946 = (

let uu____10949 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____10949))
in uu____10946.FStar_Syntax_Syntax.n)
in (match (uu____10945) with
| FStar_Syntax_Syntax.Tm_type (uu____10950) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____10954 = (

let uu____10955 = (FStar_Util.set_is_empty free)
in (not (uu____10955)))
in (match (uu____10954) with
| true -> begin
(fail1 kres)
end
| uu____10956 -> begin
()
end)))
end
| uu____10957 -> begin
(fail1 kres)
end));
(

let a = (

let uu____10959 = (

let uu____10962 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) uu____10962))
in (FStar_Syntax_Syntax.new_bv uu____10959 kres))
in (

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Syntax.bv_to_name a)
end
| uu____10970 -> begin
(

let uu____10977 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____10977 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
end)
in ((FStar_Syntax_Util.set_uvar u.FStar_Syntax_Syntax.ctx_uvar_head t);
((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)));
)));
)
end)))
end)))))))
in (

let gen_univs1 = (gen_univs env univs1)
in (

let gen_tvars = (gen_types uvs)
in (

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____11088 -> (match (uu____11088) with
| (lbname, e, c) -> begin
(

let uu____11142 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____11217 -> begin
(

let uu____11232 = ((e), (c))
in (match (uu____11232) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____11283 -> (match (uu____11283) with
| (x, uu____11291) -> begin
(

let uu____11296 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____11296))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____11314 = (

let uu____11315 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____11315))
in (match (uu____11314) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____11318 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____11319 -> begin
e1
end)
in (

let t = (

let uu____11321 = (

let uu____11322 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____11322.FStar_Syntax_Syntax.n)
in (match (uu____11321) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____11343 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____11343) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____11356 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____11360 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____11360), (gen_tvars))))))))
end))
end)
in (match (uu____11142) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____11514 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____11514) with
| true -> begin
(

let uu____11515 = (

let uu____11516 = (FStar_List.map (fun uu____11529 -> (match (uu____11529) with
| (lb, uu____11537, uu____11538) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____11516 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____11515))
end
| uu____11541 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____11559 -> (match (uu____11559) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____11588 = (gen env is_rec lecs)
in (match (uu____11588) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____11687 -> (match (uu____11687) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____11749 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____11749) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____11795 -> (match (uu____11795) with
| (l, us, e, c, gvs) -> begin
(

let uu____11829 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____11830 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____11831 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____11832 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11833 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____11829 uu____11830 uu____11831 uu____11832 uu____11833))))))
end))))
end
| uu____11834 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____11874 -> (match (uu____11874) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____11918 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____11918), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check1 = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____11974 -> begin
(

let uu____11975 = (FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21)
in (match (uu____11975) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____11981 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) uu____11981))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____11990 = (

let uu____11991 = (FStar_Syntax_Subst.compress e1)
in uu____11991.FStar_Syntax_Syntax.n)
in (match (uu____11990) with
| FStar_Syntax_Syntax.Tm_name (uu____11994) -> begin
true
end
| uu____11995 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___120_12015 = x
in {FStar_Syntax_Syntax.ppname = uu___120_12015.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_12015.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____12016 -> begin
e2
end)))
in (

let env2 = (

let uu___121_12018 = env1
in (

let uu____12019 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___121_12018.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___121_12018.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___121_12018.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___121_12018.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___121_12018.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___121_12018.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___121_12018.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___121_12018.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___121_12018.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___121_12018.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___121_12018.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___121_12018.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___121_12018.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___121_12018.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___121_12018.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___121_12018.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____12019; FStar_TypeChecker_Env.is_iface = uu___121_12018.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___121_12018.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___121_12018.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___121_12018.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___121_12018.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___121_12018.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___121_12018.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___121_12018.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___121_12018.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___121_12018.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___121_12018.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___121_12018.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___121_12018.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___121_12018.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___121_12018.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___121_12018.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___121_12018.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___121_12018.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___121_12018.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___121_12018.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___121_12018.FStar_TypeChecker_Env.dep_graph}))
in (

let uu____12020 = (check1 env2 t1 t2)
in (match (uu____12020) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12027 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____12032 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____12027 uu____12032)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____12039 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____12039) with
| true -> begin
(

let uu____12040 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____12040))
end
| uu____12041 -> begin
()
end));
(

let uu____12042 = (decorate e t2)
in ((uu____12042), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____12074 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____12074) with
| true -> begin
(

let uu____12079 = (discharge g1)
in (

let uu____12080 = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((uu____12079), (uu____12080))))
end
| uu____12081 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]
in (

let c1 = (

let uu____12087 = (

let uu____12088 = (

let uu____12089 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____12089 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____12088 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____12087 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____12091 = (destruct_comp c1)
in (match (uu____12091) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____12108 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12109 = (

let uu____12114 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____12115 = (

let uu____12116 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____12123 = (

let uu____12132 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____12132)::[])
in (uu____12116)::uu____12123))
in (FStar_Syntax_Syntax.mk_Tm_app uu____12114 uu____12115)))
in (uu____12109 FStar_Pervasives_Native.None uu____12108)))
in ((

let uu____12160 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12160) with
| true -> begin
(

let uu____12161 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____12161))
end
| uu____12162 -> begin
()
end));
(

let g2 = (

let uu____12164 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____12164))
in (

let uu____12165 = (discharge g2)
in (

let uu____12166 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____12165), (uu____12166)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___88_12198 -> (match (uu___88_12198) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____12206))::[] -> begin
(f fst1)
end
| uu____12223 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____12230 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____12230 (fun _0_21 -> FStar_TypeChecker_Common.NonTrivial (_0_21)))))
in (

let op_or_e = (fun e -> (

let uu____12237 = (

let uu____12238 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____12238))
in (FStar_All.pipe_right uu____12237 (fun _0_22 -> FStar_TypeChecker_Common.NonTrivial (_0_22)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_23 -> FStar_TypeChecker_Common.NonTrivial (_0_23))))
in (

let op_or_t = (fun t -> (

let uu____12251 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____12251 (fun _0_24 -> FStar_TypeChecker_Common.NonTrivial (_0_24)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_25 -> FStar_TypeChecker_Common.NonTrivial (_0_25))))
in (

let short_op_ite = (fun uu___89_12263 -> (match (uu___89_12263) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____12271))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____12290))::[] -> begin
(

let uu____12319 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____12319 (fun _0_26 -> FStar_TypeChecker_Common.NonTrivial (_0_26))))
end
| uu____12320 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____12331 = (

let uu____12339 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____12339)))
in (

let uu____12347 = (

let uu____12357 = (

let uu____12365 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____12365)))
in (

let uu____12373 = (

let uu____12383 = (

let uu____12391 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____12391)))
in (

let uu____12399 = (

let uu____12409 = (

let uu____12417 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____12417)))
in (

let uu____12425 = (

let uu____12435 = (

let uu____12443 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____12443)))
in (uu____12435)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____12409)::uu____12425))
in (uu____12383)::uu____12399))
in (uu____12357)::uu____12373))
in (uu____12331)::uu____12347))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____12505 = (FStar_Util.find_map table (fun uu____12520 -> (match (uu____12520) with
| (x, mk1) -> begin
(

let uu____12537 = (FStar_Ident.lid_equals x lid)
in (match (uu____12537) with
| true -> begin
(

let uu____12540 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____12540))
end
| uu____12541 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (uu____12505) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____12543 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____12549 = (

let uu____12550 = (FStar_Syntax_Util.un_uinst l)
in uu____12550.FStar_Syntax_Syntax.n)
in (match (uu____12549) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____12554 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____12584))::uu____12585 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____12596 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____12603, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____12604))))::uu____12605 -> begin
bs
end
| uu____12616 -> begin
(

let uu____12617 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____12617) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____12621 = (

let uu____12622 = (FStar_Syntax_Subst.compress t)
in uu____12622.FStar_Syntax_Syntax.n)
in (match (uu____12621) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____12626) -> begin
(

let uu____12643 = (FStar_Util.prefix_until (fun uu___90_12683 -> (match (uu___90_12683) with
| (uu____12690, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____12691))) -> begin
false
end
| uu____12694 -> begin
true
end)) bs')
in (match (uu____12643) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____12729, uu____12730) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____12802, uu____12803) -> begin
(

let uu____12876 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____12894 -> (match (uu____12894) with
| (x, uu____12902) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____12876) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____12945 -> (match (uu____12945) with
| (x, i) -> begin
(

let uu____12964 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____12964), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____12971 -> begin
bs
end))
end))
end
| uu____12972 -> begin
bs
end))
end))
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 t -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in (

let uu____13000 = (((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1)))
in (match (uu____13000) with
| true -> begin
e
end
| uu____13001 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end)))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____13027 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____13027) with
| true -> begin
e
end
| uu____13028 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____13062 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____13062) with
| true -> begin
((

let uu____13064 = (FStar_Ident.text_of_lid lident)
in (d uu____13064));
(

let uu____13065 = (FStar_Ident.text_of_lid lident)
in (

let uu____13066 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" uu____13065 uu____13066)));
)
end
| uu____13067 -> begin
()
end));
(

let fv = (

let uu____13069 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____13069 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (((FStar_Syntax_Util.mk_letbinding lbname [] FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def [] FStar_Range.dummyRange))::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____13079 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___122_13081 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___122_13081.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___122_13081.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___122_13081.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___122_13081.FStar_Syntax_Syntax.sigattrs})), (uu____13079)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (

let visibility = (fun uu___91_13097 -> (match (uu___91_13097) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____13098 -> begin
false
end))
in (

let reducibility = (fun uu___92_13104 -> (match (uu___92_13104) with
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
| uu____13105 -> begin
false
end))
in (

let assumption = (fun uu___93_13111 -> (match (uu___93_13111) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____13112 -> begin
false
end))
in (

let reification = (fun uu___94_13118 -> (match (uu___94_13118) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____13119) -> begin
true
end
| uu____13120 -> begin
false
end))
in (

let inferred = (fun uu___95_13126 -> (match (uu___95_13126) with
| FStar_Syntax_Syntax.Discriminator (uu____13127) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____13128) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____13133) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____13142) -> begin
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
| uu____13151 -> begin
false
end))
in (

let has_eq = (fun uu___96_13157 -> (match (uu___96_13157) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____13158 -> begin
false
end))
in (

let quals_combo_ok = (fun quals q -> (match (q) with
| FStar_Syntax_Syntax.Assumption -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (inferred x)) || (visibility x)) || (assumption x)) || (env.FStar_TypeChecker_Env.is_iface && (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction))) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)))))
end
| FStar_Syntax_Syntax.New -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((Prims.op_Equality x q) || (inferred x)) || (visibility x)) || (assumption x)))))
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (visibility x)) || (reducibility x)) || (reification x)) || (inferred x)) || (env.FStar_TypeChecker_Env.is_iface && (Prims.op_Equality x FStar_Syntax_Syntax.Assumption))) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)))))
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Visible_default -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Irreducible -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Abstract -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Noeq -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Unopteq -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.TotalEffect -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((Prims.op_Equality x q) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Logic -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)) || (inferred x)) || (visibility x)) || (reducibility x)))))
end
| FStar_Syntax_Syntax.Reifiable -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Reflectable (uu____13222) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____13227 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____13231 = (

let uu____13232 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___97_13236 -> (match (uu___97_13236) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____13237 -> begin
false
end))))
in (FStar_All.pipe_right uu____13232 Prims.op_Negation))
in (match (uu____13231) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____13252 = (

let uu____13257 = (

let uu____13258 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____13258 msg))
in ((FStar_Errors.Fatal_QulifierListNotPermitted), (uu____13257)))
in (FStar_Errors.raise_error uu____13252 r)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____13270 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____13272 -> begin
()
end);
(

let uu____13274 = (

let uu____13275 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____13275)))
in (match (uu____13274) with
| true -> begin
(err "ill-formed combination")
end
| uu____13278 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____13280), uu____13281) -> begin
((

let uu____13291 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____13291) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____13294 -> begin
()
end));
(

let uu____13295 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____13295) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____13300 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____13301) -> begin
(

let uu____13310 = (

let uu____13311 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____13311)))
in (match (uu____13310) with
| true -> begin
(err'1 ())
end
| uu____13316 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____13317) -> begin
(

let uu____13324 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____13324) with
| true -> begin
(err'1 ())
end
| uu____13327 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____13328) -> begin
(

let uu____13335 = (

let uu____13336 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____13336)))
in (match (uu____13335) with
| true -> begin
(err'1 ())
end
| uu____13341 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____13342) -> begin
(

let uu____13343 = (

let uu____13344 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____13344)))
in (match (uu____13343) with
| true -> begin
(err'1 ())
end
| uu____13349 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____13350) -> begin
(

let uu____13351 = (

let uu____13352 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____13352)))
in (match (uu____13351) with
| true -> begin
(err'1 ())
end
| uu____13357 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____13358) -> begin
(

let uu____13371 = (

let uu____13372 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____13372)))
in (match (uu____13371) with
| true -> begin
(err'1 ())
end
| uu____13377 -> begin
()
end))
end
| uu____13378 -> begin
()
end);
))))))
end
| uu____13379 -> begin
()
end)))))))))))


let must_erase_for_extraction : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun g t -> (

let rec aux_whnf = (fun env t1 -> (

let uu____13412 = (

let uu____13413 = (FStar_Syntax_Subst.compress t1)
in uu____13413.FStar_Syntax_Syntax.n)
in (match (uu____13412) with
| FStar_Syntax_Syntax.Tm_type (uu____13416) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (

let uu____13419 = (

let uu____13424 = (FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv)
in (FStar_All.pipe_right uu____13424 (FStar_TypeChecker_Env.lookup_attrs_of_lid g)))
in (FStar_All.pipe_right uu____13419 (fun l_opt -> ((FStar_Util.is_some l_opt) && (

let uu____13442 = (FStar_All.pipe_right l_opt FStar_Util.must)
in (FStar_All.pipe_right uu____13442 (FStar_List.existsb (fun t2 -> (

let uu____13459 = (

let uu____13460 = (FStar_Syntax_Subst.compress t2)
in uu____13460.FStar_Syntax_Syntax.n)
in (match (uu____13459) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_Ident.lid_equals fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.must_erase_for_extraction_attr) -> begin
true
end
| uu____13464 -> begin
false
end)))))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____13465) -> begin
(

let uu____13478 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____13478) with
| (bs, c) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____13504 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____13504) with
| true -> begin
(aux env1 (FStar_Syntax_Util.comp_result c))
end
| uu____13505 -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____13506; FStar_Syntax_Syntax.index = uu____13507; FStar_Syntax_Syntax.sort = t2}, uu____13509) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____13517, uu____13518) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____13560)::[]) -> begin
(

let uu____13591 = (

let uu____13592 = (FStar_Syntax_Util.un_uinst head1)
in uu____13592.FStar_Syntax_Syntax.n)
in (match (uu____13591) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
end
| uu____13596 -> begin
false
end))
end
| uu____13597 -> begin
false
end)))
and aux = (fun env t1 -> (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Iota)::[]) env t1)
in (

let res = (aux_whnf env t2)
in ((

let uu____13605 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Extraction")))
in (match (uu____13605) with
| true -> begin
(

let uu____13606 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "must_erase=%s: %s\n" (match (res) with
| true -> begin
"true"
end
| uu____13607 -> begin
"false"
end) uu____13606))
end
| uu____13608 -> begin
()
end));
res;
))))
in (aux g t)))




