
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (

let uu____12 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____13 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.report uu____12 uu____13))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____17 = (

let uu____18 = (FStar_Syntax_Subst.compress t)
in uu____18.FStar_Syntax_Syntax.n)
in (match (uu____17) with
| FStar_Syntax_Syntax.Tm_type (uu____21) -> begin
true
end
| uu____22 -> begin
false
end)))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env -> (

let uu____29 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____29 (FStar_List.filter (fun uu____35 -> (match (uu____35) with
| (x, uu____39) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = (

let uu____49 = ((FStar_Options.full_context_dependency ()) || (

let uu____50 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____50)))
in (match (uu____49) with
| true -> begin
(FStar_TypeChecker_Env.all_binders env)
end
| uu____51 -> begin
(t_binders env)
end))
in (

let uu____52 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar uu____52 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (

let uu____59 = (new_uvar_aux env k)
in (Prims.fst uu____59)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___94_64 -> (match (uu___94_64) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, uu____66); FStar_Syntax_Syntax.tk = uu____67; FStar_Syntax_Syntax.pos = uu____68; FStar_Syntax_Syntax.vars = uu____69} -> begin
uv
end
| uu____84 -> begin
(failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (

let uu____103 = (FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)
in (match (uu____103) with
| Some ((uu____116)::((tm, uu____118))::[]) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))) None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| uu____162 -> begin
(

let uu____169 = (new_uvar_aux env k)
in (match (uu____169) with
| (t, u) -> begin
(

let g = (

let uu___114_181 = FStar_TypeChecker_Rel.trivial_guard
in (

let uu____182 = (

let uu____190 = (

let uu____197 = (as_uvar u)
in ((reason), (env), (uu____197), (t), (k), (r)))
in (uu____190)::[])
in {FStar_TypeChecker_Env.guard_f = uu___114_181.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___114_181.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___114_181.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____182}))
in (

let uu____210 = (

let uu____214 = (

let uu____217 = (as_uvar u)
in ((uu____217), (r)))
in (uu____214)::[])
in ((t), (uu____210), (g))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____235 = (

let uu____236 = (FStar_Util.set_is_empty uvs)
in (not (uu____236)))
in (match (uu____235) with
| true -> begin
(

let us = (

let uu____240 = (

let uu____242 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun uu____258 -> (match (uu____258) with
| (x, uu____266) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) uu____242))
in (FStar_All.pipe_right uu____240 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____283 = (

let uu____284 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____284))
in (FStar_Errors.report r uu____283));
(FStar_Options.pop ());
))
end
| uu____285 -> begin
()
end))))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (

let uu____293 = (FStar_ST.read s.FStar_Syntax_Syntax.tk)
in (match (uu____293) with
| None -> begin
(

let uu____298 = (

let uu____299 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (

let uu____300 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" uu____299 uu____300)))
in (failwith uu____298))
end
| Some (tk) -> begin
tk
end)))


let force_sort = (fun s -> (

let uu____315 = (

let uu____318 = (force_sort' s)
in (FStar_Syntax_Syntax.mk uu____318))
in (uu____315 None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____335 -> (match (uu____335) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____342; FStar_Syntax_Syntax.lbdef = e} -> begin
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
| uu____363 -> begin
()
end);
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder1 = (fun scope a -> (

let uu____374 = (

let uu____375 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in uu____375.FStar_Syntax_Syntax.n)
in (match (uu____374) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____380 = (FStar_Syntax_Util.type_u ())
in (match (uu____380) with
| (k, uu____386) -> begin
(

let t2 = (

let uu____388 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right uu____388 Prims.fst))
in (((

let uu___115_393 = a
in {FStar_Syntax_Syntax.ppname = uu___115_393.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_393.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (false)))
end))
end
| uu____394 -> begin
((a), (true))
end)))
in (

let rec aux = (fun must_check_ty vars e1 -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e3, uu____419) -> begin
(aux must_check_ty vars e3)
end
| FStar_Syntax_Syntax.Tm_ascribed (e3, t2, uu____426) -> begin
(((Prims.fst t2)), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____472) -> begin
(

let uu____495 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____519 uu____520 -> (match (((uu____519), (uu____520))) with
| ((scope, bs1, must_check_ty1), (a, imp)) -> begin
(

let uu____562 = (match (must_check_ty1) with
| true -> begin
((a), (true))
end
| uu____567 -> begin
(mk_binder1 scope a)
end)
in (match (uu____562) with
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
in (match (uu____495) with
| (scope, bs1, must_check_ty1) -> begin
(

let uu____623 = (aux must_check_ty1 scope body)
in (match (uu____623) with
| (res, must_check_ty2) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____640 = (FStar_Options.ml_ish ())
in (match (uu____640) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____641 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Util.arrow bs1 c)
in ((

let uu____647 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____647) with
| true -> begin
(

let uu____648 = (FStar_Range.string_of_range r)
in (

let uu____649 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____650 = (FStar_Util.string_of_bool must_check_ty2)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" uu____648 uu____649 uu____650))))
end
| uu____651 -> begin
()
end));
((FStar_Util.Inl (t2)), (must_check_ty2));
)))
end))
end))
end
| uu____658 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end
| uu____665 -> begin
(

let uu____666 = (

let uu____669 = (

let uu____670 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____670 Prims.fst))
in FStar_Util.Inl (uu____669))
in ((uu____666), (false)))
end)
end)))
in (

let uu____677 = (

let uu____682 = (t_binders env)
in (aux false uu____682 e))
in (match (uu____677) with
| (t2, b) -> begin
(

let t3 = (match (t2) with
| FStar_Util.Inr (c) -> begin
(

let uu____699 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____699) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____702 -> begin
(

let uu____703 = (

let uu____704 = (

let uu____707 = (

let uu____708 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____708))
in ((uu____707), (rng)))
in FStar_Errors.Error (uu____704))
in (Prims.raise uu____703))
end))
end
| FStar_Util.Inl (t3) -> begin
t3
end)
in (([]), (t3), (b)))
end)))));
)
end
| uu____715 -> begin
(

let uu____716 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____716) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c))) None p1.FStar_Syntax_Syntax.p)
in (([]), ([]), ([]), (env1), (e), (p1)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____799) -> begin
(

let uu____804 = (FStar_Syntax_Util.type_u ())
in (match (uu____804) with
| (k, uu____817) -> begin
(

let t = (new_uvar env1 k)
in (

let x1 = (

let uu___116_820 = x
in {FStar_Syntax_Syntax.ppname = uu___116_820.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_820.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____821 = (

let uu____824 = (FStar_TypeChecker_Env.all_binders env1)
in (FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p uu____824 t))
in (match (uu____821) with
| (e, u) -> begin
(

let p2 = (

let uu___117_839 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.ty = uu___117_839.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___117_839.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env1), (e), (p2)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____846 = (FStar_Syntax_Util.type_u ())
in (match (uu____846) with
| (t, uu____859) -> begin
(

let x1 = (

let uu___118_861 = x
in (

let uu____862 = (new_uvar env1 t)
in {FStar_Syntax_Syntax.ppname = uu___118_861.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_861.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____862}))
in (

let env2 = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env1 x1)
end
| uu____866 -> begin
env1
end)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1))) None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (p1)))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____884 = (FStar_Syntax_Util.type_u ())
in (match (uu____884) with
| (t, uu____897) -> begin
(

let x1 = (

let uu___119_899 = x
in (

let uu____900 = (new_uvar env1 t)
in {FStar_Syntax_Syntax.ppname = uu___119_899.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_899.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____900}))
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x1)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1))) None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ((x1)::[]), ([]), (env2), (e), (p1)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____932 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____988 uu____989 -> (match (((uu____988), (uu____989))) with
| ((b, a, w, env2, args, pats1), (p2, imp)) -> begin
(

let uu____1088 = (pat_as_arg_with_env allow_wc_dependence env2 p2)
in (match (uu____1088) with
| (b', a', w', env3, te, pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1127 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), ((((pat), (imp)))::pats1)))
end))
end)) (([]), ([]), ([]), (env1), ([]), ([]))))
in (match (uu____932) with
| (b, a, w, env2, args, pats1) -> begin
(

let e = (

let uu____1196 = (

let uu____1199 = (

let uu____1200 = (

let uu____1205 = (

let uu____1208 = (

let uu____1209 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____1210 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____1209 uu____1210)))
in (uu____1208 None p1.FStar_Syntax_Syntax.p))
in ((uu____1205), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____1200))
in (FStar_Syntax_Syntax.mk uu____1199))
in (uu____1196 None p1.FStar_Syntax_Syntax.p))
in (

let uu____1227 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____1233 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____1239 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____1227), (uu____1233), (uu____1239), (env2), (e), ((

let uu___120_1252 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___120_1252.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___120_1252.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (uu____1258) -> begin
(failwith "impossible")
end))
in (

let rec elaborate_pat = (fun env1 p1 -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end
| uu____1298 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end))
in (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____1327 -> (match (uu____1327) with
| (p2, imp) -> begin
(

let uu____1342 = (elaborate_pat env1 p2)
in ((uu____1342), (imp)))
end)) pats)
in (

let uu____1347 = (FStar_TypeChecker_Env.lookup_datacon env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1347) with
| (uu____1356, t) -> begin
(

let uu____1358 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1358) with
| (f, uu____1369) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____1444)::uu____1445) -> begin
(Prims.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((uu____1480)::uu____1481, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____1521 -> (match (uu____1521) with
| (t1, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____1539 = (

let uu____1541 = (FStar_Syntax_Syntax.range_of_bv t1)
in Some (uu____1541))
in (FStar_Syntax_Syntax.new_bv uu____1539 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____1547 = (maybe_dot inaccessible a r)
in ((uu____1547), (true)))))
end
| uu____1552 -> begin
(

let uu____1554 = (

let uu____1555 = (

let uu____1558 = (

let uu____1559 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____1559))
in ((uu____1558), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Errors.Error (uu____1555))
in (Prims.raise uu____1554))
end)
end))))
end
| ((f1)::formals', ((p2, p_imp))::pats') -> begin
(match (f1) with
| (uu____1610, Some (FStar_Syntax_Syntax.Implicit (uu____1611))) when p_imp -> begin
(

let uu____1613 = (aux formals' pats')
in (((p2), (true)))::uu____1613)
end
| (uu____1625, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p2.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p3 = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (

let uu____1636 = (aux formals' pats2)
in (((p3), (true)))::uu____1636)))
end
| (uu____1648, imp) -> begin
(

let uu____1652 = (

let uu____1657 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p2), (uu____1657)))
in (

let uu____1660 = (aux formals' pats')
in (uu____1652)::uu____1660))
end)
end))
in (

let uu___121_1670 = p1
in (

let uu____1673 = (

let uu____1674 = (

let uu____1682 = (aux f pats1)
in ((fv), (uu____1682)))
in FStar_Syntax_Syntax.Pat_cons (uu____1674))
in {FStar_Syntax_Syntax.v = uu____1673; FStar_Syntax_Syntax.ty = uu___121_1670.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___121_1670.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____1693 -> begin
p1
end)))
in (

let one_pat = (fun allow_wc_dependence env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____1719 = (pat_as_arg_with_env allow_wc_dependence env1 p2)
in (match (uu____1719) with
| (b, a, w, env2, arg, p3) -> begin
(

let uu____1749 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____1749) with
| Some (x) -> begin
(

let uu____1762 = (

let uu____1763 = (

let uu____1766 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in ((uu____1766), (p3.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____1763))
in (Prims.raise uu____1762))
end
| uu____1775 -> begin
((b), (a), (w), (arg), (p3))
end))
end))))
in (

let top_level_pat_as_args = (fun env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((q)::pats) -> begin
(

let uu____1818 = (one_pat false env1 q)
in (match (uu____1818) with
| (b, a, uu____1834, te, q1) -> begin
(

let uu____1843 = (FStar_List.fold_right (fun p2 uu____1859 -> (match (uu____1859) with
| (w, args, pats1) -> begin
(

let uu____1883 = (one_pat false env1 p2)
in (match (uu____1883) with
| (b', a', w', arg, p3) -> begin
(

let uu____1909 = (

let uu____1910 = (FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a')
in (not (uu____1910)))
in (match (uu____1909) with
| true -> begin
(

let uu____1917 = (

let uu____1918 = (

let uu____1921 = (FStar_TypeChecker_Err.disjunctive_pattern_vars a a')
in (

let uu____1922 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____1921), (uu____1922))))
in FStar_Errors.Error (uu____1918))
in (Prims.raise uu____1917))
end
| uu____1929 -> begin
(

let uu____1930 = (

let uu____1932 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____1932)::args)
in (((FStar_List.append w' w)), (uu____1930), ((p3)::pats1)))
end))
end))
end)) pats (([]), ([]), ([])))
in (match (uu____1843) with
| (w, args, pats1) -> begin
(

let uu____1953 = (

let uu____1955 = (FStar_Syntax_Syntax.as_arg te)
in (uu____1955)::args)
in (((FStar_List.append b w)), (uu____1953), ((

let uu___122_1960 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q1)::pats1); FStar_Syntax_Syntax.ty = uu___122_1960.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___122_1960.FStar_Syntax_Syntax.p}))))
end))
end))
end
| uu____1961 -> begin
(

let uu____1962 = (one_pat true env1 p1)
in (match (uu____1962) with
| (b, uu____1977, uu____1978, arg, p2) -> begin
(

let uu____1987 = (

let uu____1989 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____1989)::[])
in ((b), (uu____1987), (p2)))
end))
end))
in (

let uu____1992 = (top_level_pat_as_args env p)
in (match (uu____1992) with
| (b, args, p1) -> begin
(

let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in ((b), (exps), (p1)))
end)))))))


let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (

let qq = p
in (

let rec aux = (fun p1 e -> (

let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p1.FStar_Syntax_Syntax.p))
in (

let e1 = (FStar_Syntax_Util.unmeta e)
in (match (((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n))) with
| (uu____2063, FStar_Syntax_Syntax.Tm_uinst (e2, uu____2065)) -> begin
(aux p1 e2)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____2070), FStar_Syntax_Syntax.Tm_constant (uu____2071)) -> begin
(

let uu____2072 = (force_sort' e1)
in (pkg p1.FStar_Syntax_Syntax.v uu____2072))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____2076 = (

let uu____2077 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2078 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2077 uu____2078)))
in (failwith uu____2076))
end
| uu____2079 -> begin
()
end);
(

let uu____2081 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____2081) with
| true -> begin
(

let uu____2082 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2083 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____2082 uu____2083)))
end
| uu____2084 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___123_2087 = x
in {FStar_Syntax_Syntax.ppname = uu___123_2087.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_2087.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x1)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____2091 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____2091) with
| true -> begin
(

let uu____2092 = (

let uu____2093 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2094 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2093 uu____2094)))
in (failwith uu____2092))
end
| uu____2095 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___124_2098 = x
in {FStar_Syntax_Syntax.ppname = uu___124_2098.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_2098.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x1)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____2100), uu____2101) -> begin
(

let s = (force_sort e1)
in (

let x1 = (

let uu___125_2110 = x
in {FStar_Syntax_Syntax.ppname = uu___125_2110.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___125_2110.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x1), (e1)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____2123 = (

let uu____2124 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____2124)))
in (match (uu____2123) with
| true -> begin
(

let uu____2125 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2125))
end
| uu____2134 -> begin
()
end));
(

let uu____2135 = (force_sort' e1)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) uu____2135));
)
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
((

let uu____2206 = (

let uu____2207 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____2207 Prims.op_Negation))
in (match (uu____2206) with
| true -> begin
(

let uu____2208 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2208))
end
| uu____2217 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(

let uu____2296 = (force_sort' e1)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))) uu____2296))
end
| ((arg)::args2, ((argpat, uu____2309))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____2359)) -> begin
(

let x = (

let uu____2375 = (force_sort e2)
in (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Syntax_Syntax.p)) uu____2375))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____2389) -> begin
(

let pat = (

let uu____2404 = (aux argpat e2)
in (

let uu____2405 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____2404), (uu____2405))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____2408 -> begin
(

let uu____2422 = (

let uu____2423 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____2424 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____2423 uu____2424)))
in (failwith uu____2422))
end))
in (match_args [] args argpats)));
)
end
| uu____2431 -> begin
(

let uu____2434 = (

let uu____2435 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____2436 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____2437 = (

let uu____2438 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right uu____2438 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____2435 uu____2436 uu____2437))))
in (failwith uu____2434))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), uu____2445) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps1 = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps1)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (uu____2461, (e)::[]) -> begin
(aux p e)
end
| uu____2464 -> begin
(failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk1 = (fun f -> ((FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____2501 -> (match (uu____2501) with
| (p, i) -> begin
(

let uu____2511 = (decorated_pattern_as_term p)
in (match (uu____2511) with
| (vars, te) -> begin
(

let uu____2524 = (

let uu____2527 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____2527)))
in ((vars), (uu____2524)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____2534) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____2542 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____2542)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(

let uu____2545 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____2545)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2559 = (

let uu____2567 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____2567 FStar_List.unzip))
in (match (uu____2559) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____2625 = (

let uu____2626 = (

let uu____2627 = (

let uu____2637 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____2637), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____2627))
in (mk1 uu____2626))
in ((vars1), (uu____2625))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____2666))::[] -> begin
wp
end
| uu____2679 -> begin
(

let uu____2685 = (

let uu____2686 = (

let uu____2687 = (FStar_List.map (fun uu____2691 -> (match (uu____2691) with
| (x, uu____2695) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____2687 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____2686))
in (failwith uu____2685))
end)
in (

let uu____2699 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____2699), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____2713 = (destruct_comp c)
in (match (uu____2713) with
| (u, uu____2718, wp) -> begin
(

let uu____2720 = (

let uu____2726 = (

let uu____2727 = (lift.FStar_TypeChecker_Env.mlift_wp c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____2727))
in (uu____2726)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____2720; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____2737 = (

let uu____2741 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____2742 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____2741 uu____2742)))
in (match (uu____2737) with
| (m, uu____2744, uu____2745) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____2755 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____2755) with
| true -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| uu____2756 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____2780 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____2780) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____2802 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____2802) with
| (a, kwp) -> begin
(

let uu____2819 = (destruct_comp m1)
in (

let uu____2823 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____2819), (uu____2823))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (

let uu____2871 = (

let uu____2872 = (

let uu____2878 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2878)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____2872; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp uu____2871)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (match ((FStar_Ident.lid_equals mname FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (Some (u_result)))
end
| uu____2907 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu___126_2914 = lc
in (

let uu____2915 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___126_2914.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____2915; FStar_Syntax_Syntax.cflags = uu___126_2914.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2918 -> (

let uu____2919 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst1 uu____2919)))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2923 = (

let uu____2924 = (FStar_Syntax_Subst.compress t)
in uu____2924.FStar_Syntax_Syntax.n)
in (match (uu____2923) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2927) -> begin
true
end
| uu____2935 -> begin
false
end)))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v1 -> (

let c = (

let uu____2946 = (

let uu____2947 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____2947))
in (match (uu____2946) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____2948 -> begin
(

let m = (

let uu____2950 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must uu____2950))
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (

let uu____2954 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2954) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____2955 -> begin
(

let uu____2956 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (uu____2956) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____2962 = (

let uu____2963 = (

let uu____2964 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2965 = (

let uu____2966 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____2967 = (

let uu____2969 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____2969)::[])
in (uu____2966)::uu____2967))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2964 uu____2965)))
in (uu____2963 (Some (k.FStar_Syntax_Syntax.n)) v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env uu____2962)))
end))
end))
in ((mk_comp m) u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
in ((

let uu____2975 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____2975) with
| true -> begin
(

let uu____2976 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____2977 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____2978 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2976 uu____2977 uu____2978))))
end
| uu____2979 -> begin
()
end));
c;
)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____2995 -> (match (uu____2995) with
| (b, lc2) -> begin
(

let lc11 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc21 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc11 lc21)
in ((

let uu____3005 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____3005) with
| true -> begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____3008 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (

let uu____3010 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____3011 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" uu____3008 uu____3010 bstr uu____3011)))))
end
| uu____3012 -> begin
()
end));
(

let bind_it = (fun uu____3016 -> (

let uu____3017 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3017) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____3019 -> begin
(

let c1 = (lc11.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc21.FStar_Syntax_Syntax.comp ())
in ((

let uu____3027 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____3027) with
| true -> begin
(

let uu____3028 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____3030 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____3031 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____3032 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (

let uu____3033 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" uu____3028 uu____3030 uu____3031 uu____3032 uu____3033))))))
end
| uu____3034 -> begin
()
end));
(

let try_simplify = (fun uu____3041 -> (

let aux = (fun uu____3050 -> (

let uu____3051 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____3051) with
| true -> begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (uu____3068) -> begin
(

let uu____3069 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____3069) with
| true -> begin
Some (((c2), ("trivial ml")))
end
| uu____3081 -> begin
None
end))
end)
end
| uu____3086 -> begin
(

let uu____3087 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____3087) with
| true -> begin
Some (((c2), ("both ml")))
end
| uu____3099 -> begin
None
end))
end)))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
(

let uu____3120 = (

let uu____3123 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____3123), (reason)))
in Some (uu____3120))
end
| uu____3126 -> begin
(aux ())
end))
in (

let uu____3131 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____3131) with
| true -> begin
(subst_c2 "both total")
end
| uu____3135 -> begin
(

let uu____3136 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3136) with
| true -> begin
(

let uu____3140 = (

let uu____3143 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____3143), ("both gtot")))
in Some (uu____3140))
end
| uu____3146 -> begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
(

let uu____3156 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____3157 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____3157))))
in (match (uu____3156) with
| true -> begin
(subst_c2 "substituted e")
end
| uu____3161 -> begin
(aux ())
end))
end
| uu____3162 -> begin
(aux ())
end)
end))
end)))))
in (

let uu____3167 = (try_simplify ())
in (match (uu____3167) with
| Some (c, reason) -> begin
c
end
| None -> begin
(

let uu____3177 = (lift_and_destruct env c1 c2)
in (match (uu____3177) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(

let uu____3211 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____3211)::[])
end
| Some (x) -> begin
(

let uu____3213 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3213)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r11 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)))) None r1)
in (

let wp_args = (

let uu____3240 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____3241 = (

let uu____3243 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3244 = (

let uu____3246 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____3247 = (

let uu____3249 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____3250 = (

let uu____3252 = (

let uu____3253 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____3253))
in (uu____3252)::[])
in (uu____3249)::uu____3250))
in (uu____3246)::uu____3247))
in (uu____3243)::uu____3244))
in (uu____3240)::uu____3241))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (

let uu____3258 = (

let uu____3259 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3259 wp_args))
in (uu____3258 None t2.FStar_Syntax_Syntax.pos))
in (

let c = ((mk_comp md) u_t2 t2 wp [])
in c)))))))
end))
end)));
)))
end)))
in {FStar_Syntax_Syntax.eff_name = joined_eff; FStar_Syntax_Syntax.res_typ = lc21.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it});
))))
end))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false)))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason1) -> begin
(

let uu____3308 = (

let uu____3309 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____3309))
in (match (uu____3308) with
| true -> begin
f
end
| uu____3310 -> begin
(

let uu____3311 = (reason1 ())
in (label uu____3311 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___127_3322 = g
in (

let uu____3323 = (

let uu____3324 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____3324))
in {FStar_TypeChecker_Env.guard_f = uu____3323; FStar_TypeChecker_Env.deferred = uu___127_3322.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___127_3322.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___127_3322.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____3334 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____3351 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3355 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3355) with
| true -> begin
c
end
| uu____3358 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____3362 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3362) with
| true -> begin
c
end
| uu____3365 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____3367 = (destruct_comp c1)
in (match (uu____3367) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____3380 = (

let uu____3381 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____3382 = (

let uu____3383 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3384 = (

let uu____3386 = (FStar_Syntax_Syntax.as_arg f1)
in (

let uu____3387 = (

let uu____3389 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3389)::[])
in (uu____3386)::uu____3387))
in (uu____3383)::uu____3384))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3381 uu____3382)))
in (uu____3380 None wp.FStar_Syntax_Syntax.pos))
in ((mk_comp md) u_res_t res_t wp1 c1.FStar_Syntax_Syntax.flags)))
end)))
end))
end)
end))))
in (

let uu___128_3394 = lc
in {FStar_Syntax_Syntax.eff_name = uu___128_3394.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___128_3394.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___128_3394.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> (

let uu____3421 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____3421) with
| true -> begin
((lc), (g0))
end
| uu____3424 -> begin
((

let uu____3426 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3426) with
| true -> begin
(

let uu____3427 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____3428 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" uu____3427 uu____3428)))
end
| uu____3429 -> begin
()
end));
(

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___95_3434 -> (match (uu___95_3434) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| uu____3436 -> begin
[]
end))))
in (

let strengthen = (fun uu____3442 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____3448 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____3450 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____3450) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c1 = (

let uu____3457 = ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (

let uu____3458 = (FStar_Syntax_Util.is_partial_return c)
in (not (uu____3458))))
in (match (uu____3457) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (

let xret = (

let uu____3465 = (

let uu____3466 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort uu____3466))
in (FStar_Syntax_Util.comp_set_flags uu____3465 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc1 = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc1.FStar_Syntax_Syntax.comp ()))))
end
| uu____3469 -> begin
c
end))
in ((

let uu____3471 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3471) with
| true -> begin
(

let uu____3472 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____3473 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____3472 uu____3473)))
end
| uu____3474 -> begin
()
end));
(

let c2 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____3476 = (destruct_comp c2)
in (match (uu____3476) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____3489 = (

let uu____3490 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____3491 = (

let uu____3492 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3493 = (

let uu____3495 = (

let uu____3496 = (

let uu____3497 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____3497 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3496))
in (

let uu____3498 = (

let uu____3500 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3500)::[])
in (uu____3495)::uu____3498))
in (uu____3492)::uu____3493))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3490 uu____3491)))
in (uu____3489 None wp.FStar_Syntax_Syntax.pos))
in ((

let uu____3506 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3506) with
| true -> begin
(

let uu____3507 = (FStar_Syntax_Print.term_to_string wp1)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" uu____3507))
end
| uu____3508 -> begin
()
end));
(

let c21 = ((mk_comp md) u_res_t res_t wp1 flags)
in c21);
)))
end)));
))
end)))
end)))
in (

let uu____3510 = (

let uu___129_3511 = lc
in (

let uu____3512 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____3513 = (

let uu____3515 = ((FStar_Syntax_Util.is_pure_lcomp lc) && (

let uu____3516 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation uu____3516)))
in (match (uu____3515) with
| true -> begin
flags
end
| uu____3518 -> begin
[]
end))
in {FStar_Syntax_Syntax.eff_name = uu____3512; FStar_Syntax_Syntax.res_typ = uu___129_3511.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu____3513; FStar_Syntax_Syntax.comp = strengthen})))
in ((uu____3510), ((

let uu___130_3519 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___130_3519.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___130_3519.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___130_3519.FStar_TypeChecker_Env.implicits}))))));
)
end)))


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let uu____3534 = (

let uu____3537 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____3538 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____3537), (uu____3538))))
in (match (uu____3534) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (

let uu____3547 = (

let uu____3548 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (

let uu____3549 = (

let uu____3550 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3551 = (

let uu____3553 = (FStar_Syntax_Syntax.as_arg yexp)
in (uu____3553)::[])
in (uu____3550)::uu____3551))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3548 uu____3549)))
in (uu____3547 None res_t.FStar_Syntax_Syntax.pos))
in (

let x_eq_y_yret = (

let uu____3561 = (

let uu____3562 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (

let uu____3563 = (

let uu____3564 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3565 = (

let uu____3567 = (

let uu____3568 = (FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3568))
in (

let uu____3569 = (

let uu____3571 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (uu____3571)::[])
in (uu____3567)::uu____3569))
in (uu____3564)::uu____3565))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3562 uu____3563)))
in (uu____3561 None res_t.FStar_Syntax_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (

let uu____3579 = (

let uu____3580 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (

let uu____3581 = (

let uu____3582 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3583 = (

let uu____3585 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3586 = (

let uu____3588 = (

let uu____3589 = (

let uu____3590 = (

let uu____3594 = (FStar_Syntax_Syntax.mk_binder y)
in (uu____3594)::[])
in (FStar_Syntax_Util.abs uu____3590 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3589))
in (uu____3588)::[])
in (uu____3585)::uu____3586))
in (uu____3582)::uu____3583))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3580 uu____3581)))
in (uu____3579 None res_t.FStar_Syntax_Syntax.pos))
in (

let lc2 = ((mk_comp md_pure) u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (

let uu____3610 = (FStar_TypeChecker_Env.get_range env)
in (bind uu____3610 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun uu____3628 -> (

let uu____3629 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3629) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end
| uu____3631 -> begin
(

let uu____3632 = (

let uu____3645 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (

let uu____3646 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____3645 uu____3646)))
in (match (uu____3632) with
| ((md, uu____3648, uu____3649), (u_res_t, res_t, wp_then), (uu____3653, uu____3654, wp_else)) -> begin
(

let ifthenelse = (fun md1 res_t1 g wp_t wp_e -> (

let uu____3683 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____3684 = (

let uu____3685 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md1 md1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3686 = (

let uu____3687 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____3688 = (

let uu____3690 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____3691 = (

let uu____3693 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____3694 = (

let uu____3696 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____3696)::[])
in (uu____3693)::uu____3694))
in (uu____3690)::uu____3691))
in (uu____3687)::uu____3688))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3685 uu____3686)))
in (uu____3684 None uu____3683))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let uu____3704 = (

let uu____3705 = (FStar_Options.split_cases ())
in (uu____3705 > (Prims.parse_int "0")))
in (match (uu____3704) with
| true -> begin
(

let comp = ((mk_comp md) u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end
| uu____3707 -> begin
(

let wp1 = (

let uu____3711 = (

let uu____3712 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____3713 = (

let uu____3714 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3715 = (

let uu____3717 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3717)::[])
in (uu____3714)::uu____3715))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3712 uu____3713)))
in (uu____3711 None wp.FStar_Syntax_Syntax.pos))
in ((mk_comp md) u_res_t res_t wp1 []))
end))))
end))
end)))
in (

let uu____3722 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____3722; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____3729 = (

let uu____3730 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____3730))
in (FStar_Syntax_Syntax.fvar uu____3729 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____3750 -> (match (uu____3750) with
| (uu____3753, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun uu____3758 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____3760 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3760) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____3761 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____3780 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____3781 = (

let uu____3782 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3783 = (

let uu____3784 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____3785 = (

let uu____3787 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____3788 = (

let uu____3790 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____3791 = (

let uu____3793 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____3793)::[])
in (uu____3790)::uu____3791))
in (uu____3787)::uu____3788))
in (uu____3784)::uu____3785))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3782 uu____3783)))
in (uu____3781 None uu____3780))))
in (

let default_case = (

let post_k = (

let uu____3802 = (

let uu____3806 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____3806)::[])
in (

let uu____3807 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3802 uu____3807)))
in (

let kwp = (

let uu____3813 = (

let uu____3817 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____3817)::[])
in (

let uu____3818 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3813 uu____3818)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (

let uu____3823 = (

let uu____3827 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____3827)::[])
in (

let uu____3828 = (

let uu____3829 = (

let uu____3832 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____3832))
in (

let uu____3833 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left uu____3829 uu____3833)))
in (FStar_Syntax_Util.abs uu____3823 uu____3828 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in ((mk_comp md) u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun uu____3847 celse -> (match (uu____3847) with
| (g, cthen) -> begin
(

let uu____3853 = (

let uu____3866 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____3866 celse))
in (match (uu____3853) with
| ((md, uu____3868, uu____3869), (uu____3870, uu____3871, wp_then), (uu____3873, uu____3874, wp_else)) -> begin
(

let uu____3885 = (ifthenelse md res_t g wp_then wp_else)
in ((mk_comp md) u_res_t res_t uu____3885 []))
end))
end)) lcases default_case)
in (

let uu____3886 = (

let uu____3887 = (FStar_Options.split_cases ())
in (uu____3887 > (Prims.parse_int "0")))
in (match (uu____3886) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| uu____3888 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____3891 = (destruct_comp comp1)
in (match (uu____3891) with
| (uu____3895, uu____3896, wp) -> begin
(

let wp1 = (

let uu____3901 = (

let uu____3902 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____3903 = (

let uu____3904 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3905 = (

let uu____3907 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3907)::[])
in (uu____3904)::uu____3905))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3902 uu____3903)))
in (uu____3901 None wp.FStar_Syntax_Syntax.pos))
in ((mk_comp md) u_res_t res_t wp1 []))
end))))
end)))))
end))))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close1 = (fun uu____3928 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3932 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3932) with
| true -> begin
c
end
| uu____3935 -> begin
(

let uu____3936 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3936) with
| true -> begin
c
end
| uu____3939 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____3968 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3968)::[])
in (

let us = (

let uu____3971 = (

let uu____3973 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____3973)::[])
in (u_res)::uu____3971)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let uu____3984 = (

let uu____3985 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____3986 = (

let uu____3987 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3988 = (

let uu____3990 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____3991 = (

let uu____3993 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____3993)::[])
in (uu____3990)::uu____3991))
in (uu____3987)::uu____3988))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3985 uu____3986)))
in (uu____3984 None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____3999 = (destruct_comp c1)
in (match (uu____3999) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in ((mk_comp md) u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end))))
in (

let uu___131_4010 = lc
in {FStar_Syntax_Syntax.eff_name = uu___131_4010.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___131_4010.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___131_4010.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close1})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine1 = (fun uu____4025 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____4029 = ((

let uu____4030 = (is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name)
in (not (uu____4030))) || env.FStar_TypeChecker_Env.lax)
in (match (uu____4029) with
| true -> begin
c
end
| uu____4033 -> begin
(

let uu____4034 = (FStar_Syntax_Util.is_partial_return c)
in (match (uu____4034) with
| true -> begin
c
end
| uu____4037 -> begin
(

let uu____4038 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (

let uu____4039 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (not (uu____4039))))
in (match (uu____4038) with
| true -> begin
(

let uu____4042 = (

let uu____4043 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____4044 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" uu____4043 uu____4044)))
in (failwith uu____4042))
end
| uu____4047 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let t = c1.FStar_Syntax_Syntax.result_typ
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp c1)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let ret1 = (

let uu____4056 = (

let uu____4059 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____4059 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4056))
in (

let eq1 = (

let uu____4063 = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Util.mk_eq2 uu____4063 t xexp e))
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let c3 = (

let uu____4068 = (

let uu____4069 = (

let uu____4074 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c2) ((Some (x)), (eq_ret)))
in uu____4074.FStar_Syntax_Syntax.comp)
in (uu____4069 ()))
in (FStar_Syntax_Util.comp_set_flags uu____4068 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c2))))
in c3)))))))))
end))
end))
end))))
in (

let flags = (

let uu____4078 = (((

let uu____4079 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____4079))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (

let uu____4080 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____4080))))
in (match (uu____4078) with
| true -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____4082 -> begin
lc.FStar_Syntax_Syntax.cflags
end))
in (

let uu___132_4083 = lc
in {FStar_Syntax_Syntax.eff_name = uu___132_4083.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___132_4083.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine1}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____4102 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____4102) with
| None -> begin
(

let uu____4107 = (

let uu____4108 = (

let uu____4111 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____4112 = (FStar_TypeChecker_Env.get_range env)
in ((uu____4111), (uu____4112))))
in FStar_Errors.Error (uu____4108))
in (Prims.raise uu____4107))
end
| Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let uu____4133 = (

let uu____4134 = (FStar_Syntax_Subst.compress t)
in uu____4134.FStar_Syntax_Syntax.n)
in (match (uu____4133) with
| FStar_Syntax_Syntax.Tm_type (uu____4139) -> begin
(

let uu____4140 = (

let uu____4141 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in uu____4141.FStar_Syntax_Syntax.n)
in (match (uu____4140) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let uu____4147 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t1 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc1 = (

let uu____4154 = (

let uu____4155 = (

let uu____4156 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4156))
in ((None), (uu____4155)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc uu____4154))
in (

let e1 = (

let uu____4165 = (

let uu____4166 = (

let uu____4167 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4167)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4166))
in (uu____4165 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____4174 -> begin
((e), (lc))
end))
end
| uu____4175 -> begin
((e), (lc))
end)))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____4195 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____4195) with
| Some (ed) -> begin
(FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____4199 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____4208 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4208), (false)))
end
| uu____4211 -> begin
(

let uu____4212 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4212), (true)))
end)
in (match (gopt) with
| (None, uu____4218) -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___133_4221 = lc
in {FStar_Syntax_Syntax.eff_name = uu___133_4221.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___133_4221.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___133_4221.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard));
)
end
| (Some (g), apply_guard1) -> begin
(

let uu____4225 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____4225) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___134_4230 = lc
in {FStar_Syntax_Syntax.eff_name = uu___134_4230.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___134_4230.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___134_4230.FStar_Syntax_Syntax.comp})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___135_4233 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___135_4233.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___135_4233.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___135_4233.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____4239 -> (

let uu____4240 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4240) with
| true -> begin
(lc.FStar_Syntax_Syntax.comp ())
end
| uu____4243 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let uu____4245 = (

let uu____4246 = (FStar_Syntax_Subst.compress f1)
in uu____4246.FStar_Syntax_Syntax.n)
in (match (uu____4245) with
| FStar_Syntax_Syntax.Tm_abs (uu____4251, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4253; FStar_Syntax_Syntax.pos = uu____4254; FStar_Syntax_Syntax.vars = uu____4255}, uu____4256) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc1 = (

let uu___136_4280 = lc
in {FStar_Syntax_Syntax.eff_name = uu___136_4280.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___136_4280.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___136_4280.FStar_Syntax_Syntax.comp})
in (lc1.FStar_Syntax_Syntax.comp ()))
end
| uu____4281 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in ((

let uu____4286 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4286) with
| true -> begin
(

let uu____4287 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____4288 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____4289 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____4290 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____4287 uu____4288 uu____4289 uu____4290)))))
end
| uu____4291 -> begin
()
end));
(

let ct = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4293 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (uu____4293) with
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

let uu____4304 = (destruct_comp ct)
in (match (uu____4304) with
| (u_t, uu____4311, uu____4312) -> begin
(

let wp = (

let uu____4316 = (

let uu____4317 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (

let uu____4318 = (

let uu____4319 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____4320 = (

let uu____4322 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____4322)::[])
in (uu____4319)::uu____4320))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4317 uu____4318)))
in (uu____4316 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos))
in (

let cret = (

let uu____4328 = ((mk_comp md) u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4328))
in (

let guard = (match (apply_guard1) with
| true -> begin
(

let uu____4338 = (

let uu____4339 = (

let uu____4340 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____4340)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____4339))
in (uu____4338 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f1.FStar_Syntax_Syntax.pos))
end
| uu____4345 -> begin
f1
end)
in (

let uu____4346 = (

let uu____4349 = (FStar_All.pipe_left (fun _0_28 -> Some (_0_28)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____4360 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____4361 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____4349 uu____4360 e cret uu____4361))))
in (match (uu____4346) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___137_4367 = x
in {FStar_Syntax_Syntax.ppname = uu___137_4367.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___137_4367.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____4369 = (

let uu____4370 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4370))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) uu____4369 ((Some (x1)), (eq_ret))))
in (

let c2 = (c1.FStar_Syntax_Syntax.comp ())
in ((

let uu____4380 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4380) with
| true -> begin
(

let uu____4381 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____4381))
end
| uu____4382 -> begin
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

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___96_4387 -> (match (uu___96_4387) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____4389 -> begin
[]
end))))
in (

let lc1 = (

let uu___138_4391 = lc
in (

let uu____4392 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____4392; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g2 = (

let uu___139_4394 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___139_4394.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___139_4394.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___139_4394.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let uu____4414 = (

let uu____4415 = (

let uu____4416 = (

let uu____4417 = (

let uu____4418 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____4418))
in (uu____4417)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____4416))
in (uu____4415 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____4414))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____4427 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____4427) with
| true -> begin
((None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____4434 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (_)) | (FStar_Syntax_Syntax.Total (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____4451))::((ens, uu____4453))::uu____4454 -> begin
(

let uu____4476 = (

let uu____4478 = (norm req)
in Some (uu____4478))
in (

let uu____4479 = (

let uu____4480 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm uu____4480))
in ((uu____4476), (uu____4479))))
end
| uu____4482 -> begin
(

let uu____4488 = (

let uu____4489 = (

let uu____4492 = (

let uu____4493 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____4493))
in ((uu____4492), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____4489))
in (Prims.raise uu____4488))
end)
end
| uu____4497 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____4503))::uu____4504 -> begin
(

let uu____4518 = (

let uu____4521 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (FStar_All.pipe_left Prims.fst uu____4521))
in (match (uu____4518) with
| (us_r, uu____4538) -> begin
(

let uu____4539 = (

let uu____4542 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (FStar_All.pipe_left Prims.fst uu____4542))
in (match (uu____4539) with
| (us_e, uu____4559) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____4562 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4562 us_r))
in (

let as_ens = (

let uu____4564 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4564 us_e))
in (

let req = (

let uu____4568 = (

let uu____4569 = (

let uu____4570 = (

let uu____4577 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4577)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::uu____4570)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____4569))
in (uu____4568 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____4593 = (

let uu____4594 = (

let uu____4595 = (

let uu____4602 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4602)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::uu____4595)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____4594))
in (uu____4593 None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____4615 = (

let uu____4617 = (norm req)
in Some (uu____4617))
in (

let uu____4618 = (

let uu____4619 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm uu____4619))
in ((uu____4615), (uu____4618)))))))))
end))
end))
end
| uu____4621 -> begin
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
| uu____4646 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____4651 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____4651) with
| (formals, uu____4660) -> begin
(

let n_implicits = (

let uu____4672 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____4709 -> (match (uu____4709) with
| (uu____4713, imp) -> begin
((imp = None) || (imp = Some (FStar_Syntax_Syntax.Equality)))
end))))
in (match (uu____4672) with
| None -> begin
(FStar_List.length formals)
end
| Some (implicits, _first_explicit, _rest) -> begin
(FStar_List.length implicits)
end))
in n_implicits)
end)))
in (

let inst_n_binders = (fun t1 -> (

let uu____4785 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____4785) with
| None -> begin
None
end
| Some (expected_t) -> begin
(

let n_expected = (number_of_implicits expected_t)
in (

let n_available = (number_of_implicits t1)
in (match ((n_available < n_expected)) with
| true -> begin
(

let uu____4799 = (

let uu____4800 = (

let uu____4803 = (

let uu____4804 = (FStar_Util.string_of_int n_expected)
in (

let uu____4808 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____4809 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____4804 uu____4808 uu____4809))))
in (

let uu____4813 = (FStar_TypeChecker_Env.get_range env)
in ((uu____4803), (uu____4813))))
in FStar_Errors.Error (uu____4800))
in (Prims.raise uu____4799))
end
| uu____4815 -> begin
Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___97_4826 -> (match (uu___97_4826) with
| None -> begin
None
end
| Some (i) -> begin
Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4845 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4845) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (Some (_0_29), uu____4906) when (_0_29 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____4928, ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____4947 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____4947) with
| (v1, uu____4968, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____4978 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____4978) with
| (args, bs3, subst3, g') -> begin
(

let uu____5027 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____5027)))
end)))
end)))
end
| (uu____5041, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____5065 = (

let uu____5079 = (inst_n_binders t)
in (aux [] uu____5079 bs1))
in (match (uu____5065) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____5117) -> begin
((e), (torig), (guard))
end
| (uu____5133, []) when (

let uu____5149 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____5149))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____5150 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____5169 -> begin
(FStar_Syntax_Util.arrow bs2 c1)
end)
in (

let t2 = (FStar_Syntax_Subst.subst subst1 t1)
in (

let e1 = ((FStar_Syntax_Syntax.mk_Tm_app e args) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((e1), (t2), (guard)))))
end)
end)))
end))
end
| uu____5184 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs = (fun univs1 -> (

let uu____5196 = (

let uu____5198 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____5198 (FStar_List.map (fun u -> (

let uu____5208 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____5208 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____5196 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____5220 = (FStar_Util.set_is_empty x)
in (match (uu____5220) with
| true -> begin
[]
end
| uu____5222 -> begin
(

let s = (

let uu____5225 = (

let uu____5227 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____5227))
in (FStar_All.pipe_right uu____5225 FStar_Util.set_elements))
in ((

let uu____5232 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5232) with
| true -> begin
(

let uu____5233 = (

let uu____5234 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____5234))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____5233))
end
| uu____5239 -> begin
()
end));
(

let r = (

let uu____5242 = (FStar_TypeChecker_Env.get_range env)
in Some (uu____5242))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____5254 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5254) with
| true -> begin
(

let uu____5255 = (

let uu____5256 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____5256))
in (

let uu____5258 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____5259 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____5255 uu____5258 uu____5259))))
end
| uu____5260 -> begin
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

let univnames1 = (

let uu____5277 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____5277 FStar_Util.fifo_set_elements))
in univnames1))))


let maybe_set_tk = (fun ts uu___98_5304 -> (match (uu___98_5304) with
| None -> begin
ts
end
| Some (t) -> begin
(

let t1 = (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange)
in (

let t2 = (FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t1)
in ((FStar_ST.write (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t2.FStar_Syntax_Syntax.n)));
ts;
)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____5345) -> begin
generalized_univ_names
end
| (uu____5349, []) -> begin
explicit_univ_names
end
| uu____5353 -> begin
(

let uu____5358 = (

let uu____5359 = (

let uu____5362 = (

let uu____5363 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____5363))
in ((uu____5362), (t.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____5359))
in (Prims.raise uu____5358))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in (

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____5377 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5377) with
| true -> begin
(

let uu____5378 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____5378))
end
| uu____5380 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____5384 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5384) with
| true -> begin
(

let uu____5385 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" uu____5385))
end
| uu____5386 -> begin
()
end));
(

let univs2 = (check_universe_generalization univnames1 gen1 t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs2 t)
in (

let uu____5390 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs2), (ts)) uu____5390))));
));
)))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> (

let uu____5420 = (

let uu____5421 = (FStar_Util.for_all (fun uu____5426 -> (match (uu____5426) with
| (uu____5431, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation uu____5421))
in (match (uu____5420) with
| true -> begin
None
end
| uu____5448 -> begin
(

let norm = (fun c -> ((

let uu____5454 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5454) with
| true -> begin
(

let uu____5455 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____5455))
end
| uu____5456 -> begin
()
end));
(

let c1 = (

let uu____5458 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____5458) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
| uu____5459 -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end))
in ((

let uu____5461 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5461) with
| true -> begin
(

let uu____5462 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5462))
end
| uu____5463 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____5496 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____5496 FStar_Util.set_elements)))
in (

let uu____5540 = (

let uu____5558 = (FStar_All.pipe_right ecs (FStar_List.map (fun uu____5613 -> (match (uu____5613) with
| (e, c) -> begin
(

let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (

let c1 = (norm c)
in (

let t1 = (FStar_Syntax_Util.comp_result c1)
in (

let univs1 = (FStar_Syntax_Free.univs t1)
in (

let uvt = (FStar_Syntax_Free.uvars t1)
in (

let uvs = (gen_uvars uvt)
in ((univs1), (((uvs), (e), (c1))))))))))
end))))
in (FStar_All.pipe_right uu____5558 FStar_List.unzip))
in (match (uu____5540) with
| (univs1, uvars1) -> begin
(

let univs2 = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs1)
in (

let gen_univs1 = (gen_univs env univs2)
in ((

let uu____5775 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5775) with
| true -> begin
(FStar_All.pipe_right gen_univs1 (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end
| uu____5778 -> begin
()
end));
(

let ecs1 = (FStar_All.pipe_right uvars1 (FStar_List.map (fun uu____5817 -> (match (uu____5817) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____5874 -> (match (uu____5874) with
| (u, k) -> begin
(

let uu____5894 = (FStar_Unionfind.find u)
in (match (uu____5894) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (uu____5932) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____5940 -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let uu____5945 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____5945) with
| (bs, kres) -> begin
(

let a = (

let uu____5969 = (

let uu____5971 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____5971))
in (FStar_Syntax_Syntax.new_bv uu____5969 kres))
in (

let t = (

let uu____5974 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____5975 = (

let uu____5982 = (

let uu____5988 = (

let uu____5989 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp uu____5989))
in FStar_Util.Inl (uu____5988))
in Some (uu____5982))
in (FStar_Syntax_Util.abs bs uu____5974 uu____5975)))
in ((FStar_Syntax_Util.set_uvar u t);
((a), (Some (FStar_Syntax_Syntax.imp_tag)));
)))
end)))
end))
end))))
in (

let uu____6004 = (match (((tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c))
end
| ([], uu____6022) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e1), (c1))))
end
| uu____6034 -> begin
(

let uu____6042 = ((e), (c))
in (match (uu____6042) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (

let uu____6054 = (

let uu____6055 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____6055.FStar_Syntax_Syntax.n)
in (match (uu____6054) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____6072 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____6072) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs1) cod1)
end))
end
| uu____6082 -> begin
(FStar_Syntax_Util.arrow tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs tvars e1 (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c1)))))
in (

let uu____6092 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____6092)))))))
end))
end)
in (match (uu____6004) with
| (e1, c1) -> begin
((gen_univs1), (e1), (c1))
end)))
end))))
in Some (ecs1));
)))
end)))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> ((

let uu____6130 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6130) with
| true -> begin
(

let uu____6131 = (

let uu____6132 = (FStar_List.map (fun uu____6137 -> (match (uu____6137) with
| (lb, uu____6142, uu____6143) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____6132 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____6131))
end
| uu____6145 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____6153 -> (match (uu____6153) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____6168 = (

let uu____6175 = (FStar_All.pipe_right lecs (FStar_List.map (fun uu____6191 -> (match (uu____6191) with
| (uu____6197, e, c) -> begin
((e), (c))
end))))
in (gen env uu____6175))
in (match (uu____6168) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____6229 -> (match (uu____6229) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun uu____6273 uu____6274 -> (match (((uu____6273), (uu____6274))) with
| ((l, uu____6307, uu____6308), (us, e, c)) -> begin
((

let uu____6334 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____6334) with
| true -> begin
(

let uu____6335 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____6336 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____6337 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____6338 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" uu____6335 uu____6336 uu____6337 uu____6338)))))
end
| uu____6339 -> begin
()
end));
((l), (us), (e), (c));
)
end)) lecs ecs)
end))
in (FStar_List.map2 (fun univnames1 uu____6357 -> (match (uu____6357) with
| (l, generalized_univs, t, c) -> begin
(

let uu____6375 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____6375), (t), (c)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____6407 -> begin
(

let uu____6408 = (FStar_TypeChecker_Rel.try_subtype env2 t11 t21)
in (match (uu____6408) with
| None -> begin
None
end
| Some (f) -> begin
(

let uu____6412 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____6412))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____6418 = (

let uu____6419 = (FStar_Syntax_Subst.compress e1)
in uu____6419.FStar_Syntax_Syntax.n)
in (match (uu____6418) with
| FStar_Syntax_Syntax.Tm_name (uu____6422) -> begin
true
end
| uu____6423 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___140_6445 = x
in {FStar_Syntax_Syntax.ppname = uu___140_6445.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_6445.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})))) (Some (t2.FStar_Syntax_Syntax.n)) e2.FStar_Syntax_Syntax.pos)
end
| uu____6446 -> begin
(

let uu___141_6447 = e2
in (

let uu____6448 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = uu___141_6447.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu____6448; FStar_Syntax_Syntax.pos = uu___141_6447.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___141_6447.FStar_Syntax_Syntax.vars}))
end)))
in (

let env2 = (

let uu___142_6457 = env1
in (

let uu____6458 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___142_6457.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___142_6457.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___142_6457.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___142_6457.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___142_6457.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___142_6457.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___142_6457.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___142_6457.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___142_6457.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___142_6457.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___142_6457.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___142_6457.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___142_6457.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___142_6457.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___142_6457.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____6458; FStar_TypeChecker_Env.is_iface = uu___142_6457.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___142_6457.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___142_6457.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___142_6457.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___142_6457.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___142_6457.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___142_6457.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___142_6457.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____6459 = (check env2 t1 t2)
in (match (uu____6459) with
| None -> begin
(

let uu____6463 = (

let uu____6464 = (

let uu____6467 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____6468 = (FStar_TypeChecker_Env.get_range env2)
in ((uu____6467), (uu____6468))))
in FStar_Errors.Error (uu____6464))
in (Prims.raise uu____6463))
end
| Some (g) -> begin
((

let uu____6473 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____6473) with
| true -> begin
(

let uu____6474 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____6474))
end
| uu____6475 -> begin
()
end));
(

let uu____6476 = (decorate e t2)
in ((uu____6476), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____6500 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____6500) with
| true -> begin
(

let uu____6503 = (discharge g1)
in (

let uu____6504 = (lc.FStar_Syntax_Syntax.comp ())
in ((uu____6503), (uu____6504))))
end
| uu____6509 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c1 = (

let uu____6516 = (

let uu____6517 = (

let uu____6518 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____6518 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____6517 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____6516 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____6520 = (destruct_comp c1)
in (match (uu____6520) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____6532 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____6533 = (

let uu____6534 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____6535 = (

let uu____6536 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6537 = (

let uu____6539 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6539)::[])
in (uu____6536)::uu____6537))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6534 uu____6535)))
in (uu____6533 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) uu____6532)))
in ((

let uu____6545 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____6545) with
| true -> begin
(

let uu____6546 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____6546))
end
| uu____6547 -> begin
()
end));
(

let g2 = (

let uu____6549 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____6549))
in (

let uu____6550 = (discharge g2)
in (

let uu____6551 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____6550), (uu____6551)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___99_6575 -> (match (uu___99_6575) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____6581))::[] -> begin
(f fst1)
end
| uu____6594 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____6599 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____6599 (fun _0_32 -> FStar_TypeChecker_Common.NonTrivial (_0_32)))))
in (

let op_or_e = (fun e -> (

let uu____6608 = (

let uu____6611 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____6611))
in (FStar_All.pipe_right uu____6608 (fun _0_33 -> FStar_TypeChecker_Common.NonTrivial (_0_33)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_34 -> FStar_TypeChecker_Common.NonTrivial (_0_34))))
in (

let op_or_t = (fun t -> (

let uu____6622 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____6622 (fun _0_35 -> FStar_TypeChecker_Common.NonTrivial (_0_35)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_36 -> FStar_TypeChecker_Common.NonTrivial (_0_36))))
in (

let short_op_ite = (fun uu___100_6636 -> (match (uu___100_6636) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____6642))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____6657))::[] -> begin
(

let uu____6678 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____6678 (fun _0_37 -> FStar_TypeChecker_Common.NonTrivial (_0_37))))
end
| uu____6683 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____6690 = (

let uu____6695 = (short_bin_op op_and_e)
in ((FStar_Syntax_Const.op_And), (uu____6695)))
in (

let uu____6700 = (

let uu____6706 = (

let uu____6711 = (short_bin_op op_or_e)
in ((FStar_Syntax_Const.op_Or), (uu____6711)))
in (

let uu____6716 = (

let uu____6722 = (

let uu____6727 = (short_bin_op op_and_t)
in ((FStar_Syntax_Const.and_lid), (uu____6727)))
in (

let uu____6732 = (

let uu____6738 = (

let uu____6743 = (short_bin_op op_or_t)
in ((FStar_Syntax_Const.or_lid), (uu____6743)))
in (

let uu____6748 = (

let uu____6754 = (

let uu____6759 = (short_bin_op op_imp_t)
in ((FStar_Syntax_Const.imp_lid), (uu____6759)))
in (uu____6754)::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[])
in (uu____6738)::uu____6748))
in (uu____6722)::uu____6732))
in (uu____6706)::uu____6716))
in (uu____6690)::uu____6700))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____6800 = (FStar_Util.find_map table (fun uu____6806 -> (match (uu____6806) with
| (x, mk1) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
(

let uu____6819 = (mk1 seen_args)
in Some (uu____6819))
end
| uu____6820 -> begin
None
end)
end)))
in (match (uu____6800) with
| None -> begin
FStar_TypeChecker_Common.Trivial
end
| Some (g) -> begin
g
end)))
end
| uu____6822 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____6826 = (

let uu____6827 = (FStar_Syntax_Util.un_uinst l)
in uu____6827.FStar_Syntax_Syntax.n)
in (match (uu____6826) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| uu____6831 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____6849))::uu____6850 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____6856 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____6860, Some (FStar_Syntax_Syntax.Implicit (uu____6861))))::uu____6862 -> begin
bs
end
| uu____6871 -> begin
(

let uu____6872 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6872) with
| None -> begin
bs
end
| Some (t) -> begin
(

let uu____6875 = (

let uu____6876 = (FStar_Syntax_Subst.compress t)
in uu____6876.FStar_Syntax_Syntax.n)
in (match (uu____6875) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____6880) -> begin
(

let uu____6891 = (FStar_Util.prefix_until (fun uu___101_6910 -> (match (uu___101_6910) with
| (uu____6914, Some (FStar_Syntax_Syntax.Implicit (uu____6915))) -> begin
false
end
| uu____6917 -> begin
true
end)) bs')
in (match (uu____6891) with
| None -> begin
bs
end
| Some ([], uu____6935, uu____6936) -> begin
bs
end
| Some (imps, uu____6973, uu____6974) -> begin
(

let uu____7011 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____7019 -> (match (uu____7019) with
| (x, uu____7024) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____7011) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____7047 -> (match (uu____7047) with
| (x, i) -> begin
(

let uu____7058 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____7058), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____7063 -> begin
bs
end))
end))
end
| uu____7064 -> begin
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
| uu____7082 -> begin
(

let uu____7083 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t)))))))) uu____7083 e.FStar_Syntax_Syntax.pos))
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____7109 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid))
in (match (uu____7109) with
| true -> begin
e
end
| uu____7110 -> begin
(

let uu____7111 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t)))))))) uu____7111 e.FStar_Syntax_Syntax.pos))
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____7141 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____7141) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(

let uu____7143 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) uu____7143));
)
end
| uu____7144 -> begin
()
end));
(

let fv = (

let uu____7146 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____7146 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]), ([])))))
in (

let uu____7154 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv))) None FStar_Range.dummyRange)
in ((sig_ctx), (uu____7154)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___102_7176 -> (match (uu___102_7176) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7177 -> begin
false
end))
in (

let reducibility = (fun uu___103_7181 -> (match (uu___103_7181) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____7182 -> begin
false
end))
in (

let assumption = (fun uu___104_7186 -> (match (uu___104_7186) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| uu____7187 -> begin
false
end))
in (

let reification = (fun uu___105_7191 -> (match (uu___105_7191) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| uu____7193 -> begin
false
end))
in (

let inferred = (fun uu___106_7197 -> (match (uu___106_7197) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| uu____7202 -> begin
false
end))
in (

let has_eq = (fun uu___107_7206 -> (match (uu___107_7206) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| uu____7207 -> begin
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
| uu____7232 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____7235 = (

let uu____7236 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___108_7238 -> (match (uu___108_7238) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____7239 -> begin
false
end))))
in (FStar_All.pipe_right uu____7236 Prims.op_Negation))
in (match (uu____7235) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (

let uu____7249 = (

let uu____7250 = (

let uu____7253 = (

let uu____7254 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____7254 msg))
in ((uu____7253), (r)))
in FStar_Errors.Error (uu____7250))
in (Prims.raise uu____7249)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____7262 -> (err' ""))
in ((match (((FStar_List.length quals) <> (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____7268 -> begin
()
end);
(

let uu____7270 = (

let uu____7271 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____7271)))
in (match (uu____7270) with
| true -> begin
(err "ill-formed combination")
end
| uu____7273 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7275), uu____7276, uu____7277, uu____7278) -> begin
((

let uu____7291 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____7291) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____7293 -> begin
()
end));
(

let uu____7294 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____7294) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____7297 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____7298) -> begin
(

let uu____7305 = (

let uu____7306 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____7306)))
in (match (uu____7305) with
| true -> begin
(err'1 ())
end
| uu____7309 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____7310) -> begin
(

let uu____7316 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____7316) with
| true -> begin
(err'1 ())
end
| uu____7318 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____7319) -> begin
(

let uu____7324 = (

let uu____7325 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption)))))
in (not (uu____7325)))
in (match (uu____7324) with
| true -> begin
(err'1 ())
end
| uu____7328 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____7329) -> begin
(

let uu____7330 = (

let uu____7331 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____7331)))
in (match (uu____7330) with
| true -> begin
(err'1 ())
end
| uu____7334 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____7335) -> begin
(

let uu____7336 = (

let uu____7337 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____7337)))
in (match (uu____7336) with
| true -> begin
(err'1 ())
end
| uu____7340 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7341) -> begin
(

let uu____7350 = (

let uu____7351 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____7351)))
in (match (uu____7350) with
| true -> begin
(err'1 ())
end
| uu____7354 -> begin
()
end))
end
| uu____7355 -> begin
()
end);
))))))
end
| uu____7356 -> begin
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

let inst_tc = (

let uu____7412 = (

let uu____7415 = (

let uu____7416 = (

let uu____7421 = (

let uu____7422 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7422))
in ((uu____7421), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____7416))
in (FStar_Syntax_Syntax.mk uu____7415))
in (uu____7412 None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7448 -> (match (uu____7448) with
| (x, imp) -> begin
(

let uu____7455 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7455), (imp)))
end))))
in ((FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p)))
in (

let unrefined_arg_binder = (

let uu____7461 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____7461))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____7463 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational None)
in (

let uu____7470 = (

let uu____7471 = (

let uu____7472 = (

let uu____7473 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____7474 = (

let uu____7475 = (

let uu____7476 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7476))
in (uu____7475)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____7473 uu____7474)))
in (uu____7472 None p))
in (FStar_Syntax_Util.b2t uu____7471))
in (FStar_Syntax_Util.refine x uu____7470)))
in (

let uu____7481 = (

let uu___143_7482 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___143_7482.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___143_7482.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____7481)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____7492 = (FStar_List.map (fun uu____7502 -> (match (uu____7502) with
| (x, uu____7509) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____7492 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7533 -> (match (uu____7533) with
| (x, uu____7540) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((fvq <> FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____7545 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((

let uu____7549 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____7549)) || (

let uu____7550 = (

let uu____7551 = (FStar_TypeChecker_Env.current_module env)
in uu____7551.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____7550)))
in (

let quals = (

let uu____7554 = (

let uu____7556 = (

let uu____7558 = (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit))
in (match (uu____7558) with
| true -> begin
(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____7560 -> begin
[]
end))
in (

let uu____7561 = (FStar_List.filter (fun uu___109_7563 -> (match (uu___109_7563) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7564 -> begin
false
end)) iquals)
in (FStar_List.append uu____7556 uu____7561)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::[]
end
| uu____7566 -> begin
[]
end)) uu____7554))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____7577 = (

let uu____7578 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7578))
in (FStar_Syntax_Syntax.mk_Total uu____7577))
in (

let uu____7579 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____7579)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t), (quals))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid discriminator_name)}
in ((

let uu____7583 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7583) with
| true -> begin
(

let uu____7584 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____7584))
end
| uu____7585 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____7587 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Const.exp_true_bool
end
| uu____7589 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____7612 -> (match (uu____7612) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____7628 = (

let uu____7631 = (

let uu____7632 = (

let uu____7637 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((uu____7637), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____7632))
in (pos uu____7631))
in ((uu____7628), (b)))
end
| uu____7640 -> begin
(

let uu____7641 = (

let uu____7644 = (

let uu____7645 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7645))
in (pos uu____7644))
in ((uu____7641), (b)))
end))
end))))
in (

let pat_true = (

let uu____7657 = (

let uu____7660 = (

let uu____7661 = (

let uu____7669 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((uu____7669), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____7661))
in (pos uu____7660))
in ((uu____7657), (None), (FStar_Syntax_Const.exp_true_bool)))
in (

let pat_false = (

let uu____7691 = (

let uu____7694 = (

let uu____7695 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7695))
in (pos uu____7694))
in ((uu____7691), (None), (FStar_Syntax_Const.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst unrefined_arg_binder))
in (

let uu____7704 = (

let uu____7707 = (

let uu____7708 = (

let uu____7724 = (

let uu____7726 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____7727 = (

let uu____7729 = (FStar_Syntax_Util.branch pat_false)
in (uu____7729)::[])
in (uu____7726)::uu____7727))
in ((arg_exp), (uu____7724)))
in FStar_Syntax_Syntax.Tm_match (uu____7708))
in (FStar_Syntax_Syntax.mk uu____7707))
in (uu____7704 None p))))))
end)
in (

let dd = (

let uu____7740 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____7740) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____7742 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____7750 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____7752 = (

let uu____7755 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd None)
in FStar_Util.Inr (uu____7755))
in (

let uu____7756 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____7752; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____7756}))
in (

let impl = (

let uu____7760 = (

let uu____7761 = (

let uu____7769 = (

let uu____7771 = (

let uu____7772 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____7772 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____7771)::[])
in ((((false), ((lb)::[]))), (uu____7769), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____7761))
in {FStar_Syntax_Syntax.sigel = uu____7760; FStar_Syntax_Syntax.sigrng = p})
in ((

let uu____7788 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7788) with
| true -> begin
(

let uu____7789 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____7789))
end
| uu____7790 -> begin
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

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7809 -> (match (uu____7809) with
| (a, uu____7813) -> begin
(

let uu____7814 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____7814) with
| (field_name, uu____7818) -> begin
(

let field_proj_tm = (

let uu____7820 = (

let uu____7821 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7821))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7820 inst_univs))
in (

let proj = ((FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[])) None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____7837 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7846 -> (match (uu____7846) with
| (x, uu____7851) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____7853 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____7853) with
| (field_name, uu____7858) -> begin
(

let t = (

let uu____7860 = (

let uu____7861 = (

let uu____7864 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____7864))
in (FStar_Syntax_Util.arrow binders uu____7861))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____7860))
in (

let only_decl = (((

let uu____7866 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____7866)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____7867 = (

let uu____7868 = (FStar_TypeChecker_Env.current_module env)
in uu____7868.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____7867)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____7878 = (FStar_List.filter (fun uu___110_7880 -> (match (uu___110_7880) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____7881 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____7878)
end
| uu____7882 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___111_7889 -> (match (uu___111_7889) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____7890 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t), (quals1))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name)}
in ((

let uu____7894 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7894) with
| true -> begin
(

let uu____7895 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____7895))
end
| uu____7896 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____7898 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____7922 -> (match (uu____7922) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match (((i + ntps) = j)) with
| true -> begin
(

let uu____7938 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____7938), (b)))
end
| uu____7943 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____7950 = (

let uu____7953 = (

let uu____7954 = (

let uu____7959 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((uu____7959), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____7954))
in (pos uu____7953))
in ((uu____7950), (b)))
end
| uu____7962 -> begin
(

let uu____7963 = (

let uu____7966 = (

let uu____7967 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7967))
in (pos uu____7966))
in ((uu____7963), (b)))
end)
end))
end))))
in (

let pat = (

let uu____7979 = (

let uu____7982 = (

let uu____7983 = (

let uu____7991 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((uu____7991), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____7983))
in (pos uu____7982))
in (

let uu____7997 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____7979), (None), (uu____7997))))
in (

let body = (

let uu____8008 = (

let uu____8011 = (

let uu____8012 = (

let uu____8028 = (

let uu____8030 = (FStar_Syntax_Util.branch pat)
in (uu____8030)::[])
in ((arg_exp), (uu____8028)))
in FStar_Syntax_Syntax.Tm_match (uu____8012))
in (FStar_Syntax_Syntax.mk uu____8011))
in (uu____8008 None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let dd = (

let uu____8047 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____8047) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____8049 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____8051 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____8053 = (

let uu____8056 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (uu____8056))
in (

let uu____8057 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____8053; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____8057}))
in (

let impl = (

let uu____8061 = (

let uu____8062 = (

let uu____8070 = (

let uu____8072 = (

let uu____8073 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____8073 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____8072)::[])
in ((((false), ((lb)::[]))), (uu____8070), (quals1), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____8062))
in {FStar_Syntax_Syntax.sigel = uu____8061; FStar_Syntax_Syntax.sigrng = p1})
in ((

let uu____8089 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8089) with
| true -> begin
(

let uu____8090 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____8090))
end
| uu____8091 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____8093 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
)))))))
end)))
end))))
in (FStar_All.pipe_right uu____7837 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, quals, uu____8121) when (not ((FStar_Ident.lid_equals constr_lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____8126 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____8126) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____8139 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____8139) with
| (formals, uu____8149) -> begin
(

let uu____8160 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____8173 = (

let uu____8174 = (

let uu____8175 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____8175))
in (FStar_Ident.lid_equals typ_lid uu____8174))
in (match (uu____8173) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____8185, uvs', tps, typ0, uu____8189, constrs, uu____8191) -> begin
Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____8205 -> begin
(failwith "Impossible")
end)
end
| uu____8210 -> begin
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
| uu____8237 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____8160) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____8247 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____8247) with
| (indices, uu____8257) -> begin
(

let refine_domain = (

let uu____8269 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___112_8271 -> (match (uu___112_8271) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8272) -> begin
true
end
| uu____8277 -> begin
false
end))))
in (match (uu____8269) with
| true -> begin
false
end
| uu____8278 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___113_8284 -> (match (uu___113_8284) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8286, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____8293 -> begin
None
end))
in (

let uu____8294 = (FStar_Util.find_map quals filter_records)
in (match (uu____8294) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)))
in (

let iquals1 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____8300 -> begin
iquals
end)
in (

let fields = (

let uu____8302 = (FStar_Util.first_N n_typars formals)
in (match (uu____8302) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____8333 uu____8334 -> (match (((uu____8333), (uu____8334))) with
| ((x, uu____8344), (x', uu____8346)) -> begin
(

let uu____8351 = (

let uu____8356 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____8356)))
in FStar_Syntax_Syntax.NT (uu____8351))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____8357 -> begin
[]
end))




