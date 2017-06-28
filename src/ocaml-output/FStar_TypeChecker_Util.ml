
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (

let uu____14 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____15 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.err uu____14 uu____15))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____20 = (

let uu____21 = (FStar_Syntax_Subst.compress t)
in uu____21.FStar_Syntax_Syntax.n)
in (match (uu____20) with
| FStar_Syntax_Syntax.Tm_type (uu____24) -> begin
true
end
| uu____25 -> begin
false
end)))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env -> (

let uu____33 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____33 (FStar_List.filter (fun uu____42 -> (match (uu____42) with
| (x, uu____46) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = (

let uu____58 = ((FStar_Options.full_context_dependency ()) || (

let uu____60 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____60)))
in (match (uu____58) with
| true -> begin
(FStar_TypeChecker_Env.all_binders env)
end
| uu____61 -> begin
(t_binders env)
end))
in (

let uu____62 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar uu____62 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (

let uu____71 = (new_uvar_aux env k)
in (FStar_Pervasives_Native.fst uu____71)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___99_77 -> (match (uu___99_77) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, uu____79); FStar_Syntax_Syntax.tk = uu____80; FStar_Syntax_Syntax.pos = uu____81; FStar_Syntax_Syntax.vars = uu____82} -> begin
uv
end
| uu____101 -> begin
(failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (

let uu____124 = (FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid)
in (match (uu____124) with
| FStar_Pervasives_Native.Some ((uu____137)::((tm, uu____139))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| uu____179 -> begin
(

let uu____186 = (new_uvar_aux env k)
in (match (uu____186) with
| (t, u) -> begin
(

let g = (

let uu___119_198 = FStar_TypeChecker_Rel.trivial_guard
in (

let uu____199 = (

let uu____207 = (

let uu____214 = (as_uvar u)
in ((reason), (env), (uu____214), (t), (k), (r)))
in (uu____207)::[])
in {FStar_TypeChecker_Env.guard_f = uu___119_198.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___119_198.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___119_198.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____199}))
in (

let uu____227 = (

let uu____231 = (

let uu____234 = (as_uvar u)
in ((uu____234), (r)))
in (uu____231)::[])
in ((t), (uu____227), (g))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____254 = (

let uu____255 = (FStar_Util.set_is_empty uvs)
in (not (uu____255)))
in (match (uu____254) with
| true -> begin
(

let us = (

let uu____259 = (

let uu____261 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun uu____272 -> (match (uu____272) with
| (x, uu____276) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) uu____261))
in (FStar_All.pipe_right uu____259 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____282 = (

let uu____283 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____283))
in (FStar_Errors.err r uu____282));
(FStar_Options.pop ());
))
end
| uu____284 -> begin
()
end))))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (

let uu____293 = (FStar_ST.read s.FStar_Syntax_Syntax.tk)
in (match (uu____293) with
| FStar_Pervasives_Native.None -> begin
(

let uu____298 = (

let uu____299 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (

let uu____300 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" uu____299 uu____300)))
in (failwith uu____298))
end
| FStar_Pervasives_Native.Some (tk) -> begin
tk
end)))


let force_sort = (fun s -> (

let uu____317 = (

let uu____320 = (force_sort' s)
in (FStar_Syntax_Syntax.mk uu____320))
in (uu____317 FStar_Pervasives_Native.None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____339 -> (match (uu____339) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____346; FStar_Syntax_Syntax.lbdef = e} -> begin
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
| uu____367 -> begin
()
end);
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder1 = (fun scope a -> (

let uu____378 = (

let uu____379 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in uu____379.FStar_Syntax_Syntax.n)
in (match (uu____378) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____384 = (FStar_Syntax_Util.type_u ())
in (match (uu____384) with
| (k, uu____390) -> begin
(

let t2 = (

let uu____392 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right uu____392 FStar_Pervasives_Native.fst))
in (((

let uu___120_398 = a
in {FStar_Syntax_Syntax.ppname = uu___120_398.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_398.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (false)))
end))
end
| uu____399 -> begin
((a), (true))
end)))
in (

let rec aux = (fun must_check_ty vars e1 -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e3, uu____424) -> begin
(aux must_check_ty vars e3)
end
| FStar_Syntax_Syntax.Tm_ascribed (e3, t2, uu____431) -> begin
(((FStar_Pervasives_Native.fst t2)), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____477) -> begin
(

let uu____490 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____527 uu____528 -> (match (((uu____527), (uu____528))) with
| ((scope, bs1, must_check_ty1), (a, imp)) -> begin
(

let uu____570 = (match (must_check_ty1) with
| true -> begin
((a), (true))
end
| uu____575 -> begin
(mk_binder1 scope a)
end)
in (match (uu____570) with
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
in (match (uu____490) with
| (scope, bs1, must_check_ty1) -> begin
(

let uu____631 = (aux must_check_ty1 scope body)
in (match (uu____631) with
| (res, must_check_ty2) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____648 = (FStar_Options.ml_ish ())
in (match (uu____648) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____649 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Util.arrow bs1 c)
in ((

let uu____655 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____655) with
| true -> begin
(

let uu____656 = (FStar_Range.string_of_range r)
in (

let uu____657 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____658 = (FStar_Util.string_of_bool must_check_ty2)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" uu____656 uu____657 uu____658))))
end
| uu____659 -> begin
()
end));
((FStar_Util.Inl (t2)), (must_check_ty2));
)))
end))
end))
end
| uu____666 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end
| uu____673 -> begin
(

let uu____674 = (

let uu____677 = (

let uu____678 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____678 FStar_Pervasives_Native.fst))
in FStar_Util.Inl (uu____677))
in ((uu____674), (false)))
end)
end)))
in (

let uu____685 = (

let uu____690 = (t_binders env)
in (aux false uu____690 e))
in (match (uu____685) with
| (t2, b) -> begin
(

let t3 = (match (t2) with
| FStar_Util.Inr (c) -> begin
(

let uu____707 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____707) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____710 -> begin
(

let uu____711 = (

let uu____712 = (

let uu____715 = (

let uu____716 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____716))
in ((uu____715), (rng)))
in FStar_Errors.Error (uu____712))
in (FStar_Pervasives.raise uu____711))
end))
end
| FStar_Util.Inl (t3) -> begin
t3
end)
in (([]), (t3), (b)))
end)))));
)
end
| uu____723 -> begin
(

let uu____724 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____724) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____795) -> begin
(

let uu____800 = (FStar_Syntax_Util.type_u ())
in (match (uu____800) with
| (k, uu____813) -> begin
(

let t = (new_uvar env1 k)
in (

let x1 = (

let uu___121_816 = x
in {FStar_Syntax_Syntax.ppname = uu___121_816.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_816.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____817 = (

let uu____820 = (FStar_TypeChecker_Env.all_binders env1)
in (FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p uu____820 t))
in (match (uu____817) with
| (e, u) -> begin
(

let p2 = (

let uu___122_834 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.p = uu___122_834.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env1), (e), (p2)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____840 = (FStar_Syntax_Util.type_u ())
in (match (uu____840) with
| (t, uu____853) -> begin
(

let x1 = (

let uu___123_855 = x
in (

let uu____856 = (new_uvar env1 t)
in {FStar_Syntax_Syntax.ppname = uu___123_855.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_855.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____856}))
in (

let env2 = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env1 x1)
end
| uu____860 -> begin
env1
end)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (p1)))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____874 = (FStar_Syntax_Util.type_u ())
in (match (uu____874) with
| (t, uu____887) -> begin
(

let x1 = (

let uu___124_889 = x
in (

let uu____890 = (new_uvar env1 t)
in {FStar_Syntax_Syntax.ppname = uu___124_889.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_889.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____890}))
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x1)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ((x1)::[]), ([]), (env2), (e), (p1)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____916 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____989 uu____990 -> (match (((uu____989), (uu____990))) with
| ((b, a, w, env2, args, pats1), (p2, imp)) -> begin
(

let uu____1089 = (pat_as_arg_with_env allow_wc_dependence env2 p2)
in (match (uu____1089) with
| (b', a', w', env3, te, pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1128 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), ((((pat), (imp)))::pats1)))
end))
end)) (([]), ([]), ([]), (env1), ([]), ([]))))
in (match (uu____916) with
| (b, a, w, env2, args, pats1) -> begin
(

let e = (

let uu____1197 = (

let uu____1200 = (

let uu____1201 = (

let uu____1206 = (

let uu____1209 = (

let uu____1210 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____1211 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____1210 uu____1211)))
in (uu____1209 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in ((uu____1206), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____1201))
in (FStar_Syntax_Syntax.mk uu____1200))
in (uu____1197 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in (

let uu____1228 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____1234 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____1240 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____1228), (uu____1234), (uu____1240), (env2), (e), ((

let uu___125_1253 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___125_1253.FStar_Syntax_Syntax.p})))))))
end))
end))
in (

let rec elaborate_pat = (fun env1 p1 -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) r)
end
| uu____1281 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) r)
end))
in (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____1308 -> (match (uu____1308) with
| (p2, imp) -> begin
(

let uu____1319 = (elaborate_pat env1 p2)
in ((uu____1319), (imp)))
end)) pats)
in (

let uu____1322 = (FStar_TypeChecker_Env.lookup_datacon env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1322) with
| (uu____1326, t) -> begin
(

let uu____1328 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1328) with
| (f, uu____1338) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____1405)::uu____1406) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((uu____1432)::uu____1433, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____1476 -> (match (uu____1476) with
| (t1, imp) -> begin
(match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____1492 = (

let uu____1494 = (FStar_Syntax_Syntax.range_of_bv t1)
in FStar_Pervasives_Native.Some (uu____1494))
in (FStar_Syntax_Syntax.new_bv uu____1492 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____1496 = (maybe_dot inaccessible a r)
in ((uu____1496), (true)))))
end
| uu____1499 -> begin
(

let uu____1501 = (

let uu____1502 = (

let uu____1505 = (

let uu____1506 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____1506))
in ((uu____1505), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Errors.Error (uu____1502))
in (FStar_Pervasives.raise uu____1501))
end)
end))))
end
| ((f1)::formals', ((p2, p_imp))::pats') -> begin
(match (f1) with
| (uu____1546, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1547))) when p_imp -> begin
(

let uu____1549 = (aux formals' pats')
in (((p2), (true)))::uu____1549)
end
| (uu____1558, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p2.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p3 = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (

let uu____1564 = (aux formals' pats2)
in (((p3), (true)))::uu____1564)))
end
| (uu____1573, imp) -> begin
(

let uu____1577 = (

let uu____1581 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p2), (uu____1581)))
in (

let uu____1583 = (aux formals' pats')
in (uu____1577)::uu____1583))
end)
end))
in (

let uu___126_1591 = p1
in (

let uu____1593 = (

let uu____1594 = (

let uu____1601 = (aux f pats1)
in ((fv), (uu____1601)))
in FStar_Syntax_Syntax.Pat_cons (uu____1594))
in {FStar_Syntax_Syntax.v = uu____1593; FStar_Syntax_Syntax.p = uu___126_1591.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____1610 -> begin
p1
end)))
in (

let one_pat = (fun allow_wc_dependence env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____1633 = (pat_as_arg_with_env allow_wc_dependence env1 p2)
in (match (uu____1633) with
| (b, a, w, env2, arg, p3) -> begin
(

let uu____1663 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____1663) with
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____1676 = (

let uu____1677 = (

let uu____1680 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in ((uu____1680), (p3.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____1677))
in (FStar_Pervasives.raise uu____1676))
end
| uu____1689 -> begin
((b), (a), (w), (arg), (p3))
end))
end))))
in (

let uu____1694 = (one_pat true env p)
in (match (uu____1694) with
| (b, uu____1708, uu____1709, tm, p1) -> begin
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
| (uu____1747, FStar_Syntax_Syntax.Tm_uinst (e2, uu____1749)) -> begin
(aux p1 e2)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____1754), FStar_Syntax_Syntax.Tm_constant (uu____1755)) -> begin
(pkg p1.FStar_Syntax_Syntax.v)
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____1759 = (

let uu____1760 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1761 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____1760 uu____1761)))
in (failwith uu____1759))
end
| uu____1762 -> begin
()
end);
(

let uu____1764 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____1764) with
| true -> begin
(

let uu____1765 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1766 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____1765 uu____1766)))
end
| uu____1767 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___127_1770 = x
in {FStar_Syntax_Syntax.ppname = uu___127_1770.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_1770.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____1774 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____1774) with
| true -> begin
(

let uu____1775 = (

let uu____1776 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1777 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____1776 uu____1777)))
in (failwith uu____1775))
end
| uu____1778 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___128_1781 = x
in {FStar_Syntax_Syntax.ppname = uu___128_1781.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___128_1781.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____1783), uu____1784) -> begin
(

let s = (force_sort e1)
in (

let x1 = (

let uu___129_1793 = x
in {FStar_Syntax_Syntax.ppname = uu___129_1793.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_1793.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x1), (e1)))))))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____1804 = (

let uu____1805 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____1805)))
in (match (uu____1804) with
| true -> begin
(

let uu____1806 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____1806))
end
| uu____1807 -> begin
()
end));
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = uu____1818; FStar_Syntax_Syntax.pos = uu____1819; FStar_Syntax_Syntax.vars = uu____1820}, args)) -> begin
((

let uu____1845 = (

let uu____1846 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____1846 Prims.op_Negation))
in (match (uu____1845) with
| true -> begin
(

let uu____1847 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____1847))
end
| uu____1848 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____1928))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____1972)) -> begin
(

let x = (

let uu____1988 = (force_sort e2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) uu____1988))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____1999) -> begin
(

let pat = (

let uu____2014 = (aux argpat e2)
in (

let uu____2015 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____2014), (uu____2015))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____2018 -> begin
(

let uu____2031 = (

let uu____2032 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____2033 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____2032 uu____2033)))
in (failwith uu____2031))
end))
in (match_args [] args argpats)));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = uu____2041; FStar_Syntax_Syntax.pos = uu____2042; FStar_Syntax_Syntax.vars = uu____2043}, uu____2044); FStar_Syntax_Syntax.tk = uu____2045; FStar_Syntax_Syntax.pos = uu____2046; FStar_Syntax_Syntax.vars = uu____2047}, args)) -> begin
((

let uu____2076 = (

let uu____2077 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____2077 Prims.op_Negation))
in (match (uu____2076) with
| true -> begin
(

let uu____2078 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2078))
end
| uu____2079 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____2159))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____2203)) -> begin
(

let x = (

let uu____2219 = (force_sort e2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) uu____2219))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____2230) -> begin
(

let pat = (

let uu____2245 = (aux argpat e2)
in (

let uu____2246 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____2245), (uu____2246))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____2249 -> begin
(

let uu____2262 = (

let uu____2263 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____2264 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____2263 uu____2264)))
in (failwith uu____2262))
end))
in (match_args [] args argpats)));
)
end
| uu____2269 -> begin
(

let uu____2272 = (

let uu____2273 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____2274 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____2275 = (FStar_Syntax_Print.term_to_string exp)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____2273 uu____2274 uu____2275))))
in (failwith uu____2272))
end))))
in (aux p exp))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____2304 -> (match (uu____2304) with
| (p, i) -> begin
(

let uu____2314 = (decorated_pattern_as_term p)
in (match (uu____2314) with
| (vars, te) -> begin
(

let uu____2327 = (

let uu____2330 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____2330)))
in ((vars), (uu____2327)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____2338 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____2338)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____2341 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____2341)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____2344 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____2344)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2356 = (

let uu____2364 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____2364 FStar_List.unzip))
in (match (uu____2356) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____2421 = (

let uu____2422 = (

let uu____2423 = (

let uu____2433 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____2433), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____2423))
in (mk1 uu____2422))
in ((vars1), (uu____2421))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____2463))::[] -> begin
wp
end
| uu____2476 -> begin
(

let uu____2482 = (

let uu____2483 = (

let uu____2484 = (FStar_List.map (fun uu____2491 -> (match (uu____2491) with
| (x, uu____2495) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____2484 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____2483))
in (failwith uu____2482))
end)
in (

let uu____2499 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____2499), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____2516 = (destruct_comp c)
in (match (uu____2516) with
| (u, uu____2521, wp) -> begin
(

let uu____2523 = (

let uu____2529 = (

let uu____2530 = (lift.FStar_TypeChecker_Env.mlift_wp c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____2530))
in (uu____2529)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____2523; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____2543 = (

let uu____2547 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____2548 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____2547 uu____2548)))
in (match (uu____2543) with
| (m, uu____2550, uu____2551) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____2564 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____2564) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____2565 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____2592 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____2592) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____2614 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____2614) with
| (a, kwp) -> begin
(

let uu____2631 = (destruct_comp m1)
in (

let uu____2635 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____2631), (uu____2635))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (

let uu____2692 = (

let uu____2693 = (

let uu____2699 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2699)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____2693; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp uu____2692)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (match ((FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____2737 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu___130_2746 = lc
in (

let uu____2747 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___130_2746.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____2747; FStar_Syntax_Syntax.cflags = uu___130_2746.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2752 -> (

let uu____2753 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst1 uu____2753)))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2758 = (

let uu____2759 = (FStar_Syntax_Subst.compress t)
in uu____2759.FStar_Syntax_Syntax.n)
in (match (uu____2758) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2762) -> begin
true
end
| uu____2770 -> begin
false
end)))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____2785 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____2785) with
| true -> begin
c
end
| uu____2786 -> begin
(

let uu____2787 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2787) with
| true -> begin
c
end
| uu____2788 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____2823 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2823)::[])
in (

let us = (

let uu____2826 = (

let uu____2828 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____2828)::[])
in (u_res)::uu____2826)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____2832 = (

let uu____2833 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____2834 = (

let uu____2835 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____2836 = (

let uu____2838 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____2839 = (

let uu____2841 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____2841)::[])
in (uu____2838)::uu____2839))
in (uu____2835)::uu____2836))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2833 uu____2834)))
in (uu____2832 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____2847 = (destruct_comp c1)
in (match (uu____2847) with
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

let close1 = (fun uu____2873 -> (

let uu____2874 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp env bvs uu____2874)))
in (

let uu___131_2875 = lc
in {FStar_Syntax_Syntax.eff_name = uu___131_2875.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___131_2875.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___131_2875.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close1})))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v1 -> (

let c = (

let uu____2889 = (

let uu____2890 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____2890))
in (match (uu____2889) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____2891 -> begin
(

let m = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (

let uu____2895 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2895) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____2896 -> begin
(

let uu____2897 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____2897) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____2903 = (

let uu____2904 = (

let uu____2905 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2906 = (

let uu____2907 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____2908 = (

let uu____2910 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____2910)::[])
in (uu____2907)::uu____2908))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2905 uu____2906)))
in (uu____2904 (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env uu____2903)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
in ((

let uu____2916 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____2916) with
| true -> begin
(

let uu____2917 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____2918 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____2919 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2917 uu____2918 uu____2919))))
end
| uu____2920 -> begin
()
end));
c;
)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____2941 -> (match (uu____2941) with
| (b, lc2) -> begin
(

let lc11 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc21 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc11 lc21)
in ((

let uu____2951 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____2951) with
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

let uu____2954 = (match (e1opt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (

let uu____2956 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____2957 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" uu____2954 uu____2956 bstr uu____2957)))))
end
| uu____2958 -> begin
()
end));
(

let bind_it = (fun uu____2962 -> (

let uu____2963 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2963) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____2965 -> begin
(

let c1 = (lc11.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc21.FStar_Syntax_Syntax.comp ())
in ((

let uu____2973 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____2973) with
| true -> begin
(

let uu____2974 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____2976 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____2977 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____2978 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (

let uu____2979 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" uu____2974 uu____2976 uu____2977 uu____2978 uu____2979))))))
end
| uu____2980 -> begin
()
end));
(

let try_simplify = (fun uu____2990 -> (

let aux = (fun uu____3000 -> (

let uu____3001 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____3001) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____3020) -> begin
(

let uu____3021 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____3021) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____3034 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____3039 -> begin
(

let uu____3040 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____3040) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____3053 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____3076 = (

let uu____3079 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____3079), (reason)))
in FStar_Util.Inl (uu____3076))
end
| uu____3082 -> begin
(aux ())
end))
in (

let rec maybe_close = (fun t x c -> (

let uu____3097 = (

let uu____3098 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in uu____3098.FStar_Syntax_Syntax.n)
in (match (uu____3097) with
| FStar_Syntax_Syntax.Tm_refine (y, uu____3102) -> begin
(maybe_close y.FStar_Syntax_Syntax.sort x c)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____3108 -> begin
c
end)))
in (

let uu____3109 = (

let uu____3110 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____3110))
in (match (uu____3109) with
| true -> begin
(

let uu____3118 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3118) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____3131 -> begin
(

let uu____3132 = (

let uu____3133 = (

let uu____3136 = (FStar_TypeChecker_Env.get_range env)
in (("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad"), (uu____3136)))
in FStar_Errors.Error (uu____3133))
in (FStar_Pervasives.raise uu____3132))
end))
end
| uu____3143 -> begin
(

let uu____3144 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____3144) with
| true -> begin
(subst_c2 "both total")
end
| uu____3151 -> begin
(

let uu____3152 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3152) with
| true -> begin
(

let uu____3159 = (

let uu____3162 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____3162), ("both gtot")))
in FStar_Util.Inl (uu____3159))
end
| uu____3165 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____3178 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____3180 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____3180))))
in (match (uu____3178) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___132_3189 = x
in {FStar_Syntax_Syntax.ppname = uu___132_3189.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_3189.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____3190 = (

let uu____3193 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____3193), ("c1 Tot")))
in FStar_Util.Inl (uu____3190))))
end
| uu____3196 -> begin
(aux ())
end))
end
| uu____3197 -> begin
(aux ())
end)
end))
end))
end))))))
in (

let uu____3202 = (try_simplify ())
in (match (uu____3202) with
| FStar_Util.Inl (c, reason) -> begin
((

let uu____3220 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____3220) with
| true -> begin
(

let uu____3221 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____3222 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____3223 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print4 "Simplified (because %s) bind %s %s to %s\n" reason uu____3221 uu____3222 uu____3223))))
end
| uu____3224 -> begin
()
end));
c;
)
end
| FStar_Util.Inr (reason) -> begin
(

let uu____3230 = (lift_and_destruct env c1 c2)
in (match (uu____3230) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3264 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____3264)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____3266 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3266)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____3282 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____3283 = (

let uu____3285 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3286 = (

let uu____3288 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____3289 = (

let uu____3291 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____3292 = (

let uu____3294 = (

let uu____3295 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____3295))
in (uu____3294)::[])
in (uu____3291)::uu____3292))
in (uu____3288)::uu____3289))
in (uu____3285)::uu____3286))
in (uu____3282)::uu____3283))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (

let uu____3300 = (

let uu____3301 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3301 wp_args))
in (uu____3300 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
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

let uu____3352 = (

let uu____3353 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____3353))
in (match (uu____3352) with
| true -> begin
f
end
| uu____3354 -> begin
(

let uu____3355 = (reason1 ())
in (label uu____3355 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___133_3369 = g
in (

let uu____3370 = (

let uu____3371 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____3371))
in {FStar_TypeChecker_Env.guard_f = uu____3370; FStar_TypeChecker_Env.deferred = uu___133_3369.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___133_3369.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___133_3369.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____3383 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____3403 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3407 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3407) with
| true -> begin
c
end
| uu____3410 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____3414 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3414) with
| true -> begin
c
end
| uu____3417 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____3419 = (destruct_comp c1)
in (match (uu____3419) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____3432 = (

let uu____3433 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____3434 = (

let uu____3435 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3436 = (

let uu____3438 = (FStar_Syntax_Syntax.as_arg f1)
in (

let uu____3439 = (

let uu____3441 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3441)::[])
in (uu____3438)::uu____3439))
in (uu____3435)::uu____3436))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3433 uu____3434)))
in (uu____3432 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 c1.FStar_Syntax_Syntax.flags)))
end)))
end))
end)
end))))
in (

let uu___134_3446 = lc
in {FStar_Syntax_Syntax.eff_name = uu___134_3446.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___134_3446.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___134_3446.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> (

let uu____3478 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____3478) with
| true -> begin
((lc), (g0))
end
| uu____3481 -> begin
((

let uu____3483 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3483) with
| true -> begin
(

let uu____3484 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____3485 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" uu____3484 uu____3485)))
end
| uu____3486 -> begin
()
end));
(

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___100_3492 -> (match (uu___100_3492) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| uu____3494 -> begin
[]
end))))
in (

let strengthen = (fun uu____3500 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____3506 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____3508 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____3508) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c1 = (

let uu____3515 = ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (

let uu____3517 = (FStar_Syntax_Util.is_partial_return c)
in (not (uu____3517))))
in (match (uu____3515) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" FStar_Pervasives_Native.None (FStar_Syntax_Util.comp_result c))
in (

let xret = (

let uu____3524 = (

let uu____3525 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort uu____3525))
in (FStar_Syntax_Util.comp_set_flags uu____3524 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc1 = (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc1.FStar_Syntax_Syntax.comp ()))))
end
| uu____3528 -> begin
c
end))
in ((

let uu____3530 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3530) with
| true -> begin
(

let uu____3531 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____3532 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____3531 uu____3532)))
end
| uu____3533 -> begin
()
end));
(

let c2 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____3535 = (destruct_comp c2)
in (match (uu____3535) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____3548 = (

let uu____3549 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____3550 = (

let uu____3551 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3552 = (

let uu____3554 = (

let uu____3555 = (

let uu____3556 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____3556 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3555))
in (

let uu____3557 = (

let uu____3559 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3559)::[])
in (uu____3554)::uu____3557))
in (uu____3551)::uu____3552))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3549 uu____3550)))
in (uu____3548 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in ((

let uu____3565 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3565) with
| true -> begin
(

let uu____3566 = (FStar_Syntax_Print.term_to_string wp1)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" uu____3566))
end
| uu____3567 -> begin
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

let uu____3569 = (

let uu___135_3570 = lc
in (

let uu____3571 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____3572 = (

let uu____3574 = ((FStar_Syntax_Util.is_pure_lcomp lc) && (

let uu____3576 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation uu____3576)))
in (match (uu____3574) with
| true -> begin
flags
end
| uu____3578 -> begin
[]
end))
in {FStar_Syntax_Syntax.eff_name = uu____3571; FStar_Syntax_Syntax.res_typ = uu___135_3570.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu____3572; FStar_Syntax_Syntax.comp = strengthen})))
in ((uu____3569), ((

let uu___136_3580 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___136_3580.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___136_3580.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___136_3580.FStar_TypeChecker_Env.implicits}))))));
)
end)))


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____3598 = (

let uu____3601 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____3602 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____3601), (uu____3602))))
in (match (uu____3598) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (

let uu____3611 = (

let uu____3612 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (

let uu____3613 = (

let uu____3614 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3615 = (

let uu____3617 = (FStar_Syntax_Syntax.as_arg yexp)
in (uu____3617)::[])
in (uu____3614)::uu____3615))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3612 uu____3613)))
in (uu____3611 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let x_eq_y_yret = (

let uu____3625 = (

let uu____3626 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (

let uu____3627 = (

let uu____3628 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3629 = (

let uu____3631 = (

let uu____3632 = (FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3632))
in (

let uu____3633 = (

let uu____3635 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (uu____3635)::[])
in (uu____3631)::uu____3633))
in (uu____3628)::uu____3629))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3626 uu____3627)))
in (uu____3625 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (

let uu____3643 = (

let uu____3644 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (

let uu____3645 = (

let uu____3646 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3647 = (

let uu____3649 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3650 = (

let uu____3652 = (

let uu____3653 = (

let uu____3654 = (

let uu____3655 = (FStar_Syntax_Syntax.mk_binder y)
in (uu____3655)::[])
in (FStar_Syntax_Util.abs uu____3654 x_eq_y_yret (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3653))
in (uu____3652)::[])
in (uu____3649)::uu____3650))
in (uu____3646)::uu____3647))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3644 uu____3645)))
in (uu____3643 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (

let uu____3664 = (FStar_TypeChecker_Env.get_range env)
in (bind uu____3664 env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp comp) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun uu____3686 -> (

let uu____3687 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3687) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end
| uu____3689 -> begin
(

let uu____3690 = (

let uu____3703 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (

let uu____3704 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____3703 uu____3704)))
in (match (uu____3690) with
| ((md, uu____3706, uu____3707), (u_res_t, res_t, wp_then), (uu____3711, uu____3712, wp_else)) -> begin
(

let ifthenelse = (fun md1 res_t1 g wp_t wp_e -> (

let uu____3741 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____3742 = (

let uu____3743 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md1 md1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3744 = (

let uu____3745 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____3746 = (

let uu____3748 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____3749 = (

let uu____3751 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____3752 = (

let uu____3754 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____3754)::[])
in (uu____3751)::uu____3752))
in (uu____3748)::uu____3749))
in (uu____3745)::uu____3746))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3743 uu____3744)))
in (uu____3742 FStar_Pervasives_Native.None uu____3741))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let uu____3762 = (

let uu____3763 = (FStar_Options.split_cases ())
in (uu____3763 > (Prims.parse_int "0")))
in (match (uu____3762) with
| true -> begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end
| uu____3765 -> begin
(

let wp1 = (

let uu____3769 = (

let uu____3770 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____3771 = (

let uu____3772 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3773 = (

let uu____3775 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3775)::[])
in (uu____3772)::uu____3773))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3770 uu____3771)))
in (uu____3769 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end))
end)))
in (

let uu____3780 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____3780; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____3789 = (

let uu____3790 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____3790))
in (FStar_Syntax_Syntax.fvar uu____3789 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____3817 -> (match (uu____3817) with
| (uu____3820, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun uu____3825 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____3827 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3827) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____3828 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____3847 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____3848 = (

let uu____3849 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3850 = (

let uu____3851 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____3852 = (

let uu____3854 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____3855 = (

let uu____3857 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____3858 = (

let uu____3860 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____3860)::[])
in (uu____3857)::uu____3858))
in (uu____3854)::uu____3855))
in (uu____3851)::uu____3852))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3849 uu____3850)))
in (uu____3848 FStar_Pervasives_Native.None uu____3847))))
in (

let default_case = (

let post_k = (

let uu____3869 = (

let uu____3873 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____3873)::[])
in (

let uu____3874 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3869 uu____3874)))
in (

let kwp = (

let uu____3880 = (

let uu____3884 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____3884)::[])
in (

let uu____3885 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3880 uu____3885)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____3890 = (

let uu____3891 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____3891)::[])
in (

let uu____3892 = (

let uu____3893 = (

let uu____3896 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____3896))
in (

let uu____3897 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____3893 uu____3897)))
in (FStar_Syntax_Util.abs uu____3890 uu____3892 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun uu____3919 celse -> (match (uu____3919) with
| (g, cthen) -> begin
(

let uu____3925 = (

let uu____3938 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____3938 celse))
in (match (uu____3925) with
| ((md, uu____3940, uu____3941), (uu____3942, uu____3943, wp_then), (uu____3945, uu____3946, wp_else)) -> begin
(

let uu____3957 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____3957 []))
end))
end)) lcases default_case)
in (

let uu____3958 = (

let uu____3959 = (FStar_Options.split_cases ())
in (uu____3959 > (Prims.parse_int "0")))
in (match (uu____3958) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| uu____3960 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____3963 = (destruct_comp comp1)
in (match (uu____3963) with
| (uu____3967, uu____3968, wp) -> begin
(

let wp1 = (

let uu____3973 = (

let uu____3974 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____3975 = (

let uu____3976 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3977 = (

let uu____3979 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3979)::[])
in (uu____3976)::uu____3977))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3974 uu____3975)))
in (uu____3973 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end)))))
end))))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let flags = (

let uu____3998 = (((

let uu____4001 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____4001))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (

let uu____4003 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____4003))))
in (match (uu____3998) with
| true -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____4005 -> begin
lc.FStar_Syntax_Syntax.cflags
end))
in (

let refine1 = (fun uu____4011 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____4015 = ((

let uu____4018 = (is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name)
in (not (uu____4018))) || env.FStar_TypeChecker_Env.lax)
in (match (uu____4015) with
| true -> begin
c
end
| uu____4021 -> begin
(

let uu____4022 = (FStar_Syntax_Util.is_partial_return c)
in (match (uu____4022) with
| true -> begin
c
end
| uu____4025 -> begin
(

let uu____4026 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____4026) with
| true -> begin
(

let uu____4029 = (

let uu____4030 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (not (uu____4030)))
in (match (uu____4029) with
| true -> begin
(

let uu____4033 = (

let uu____4034 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____4035 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" uu____4034 uu____4035)))
in (failwith uu____4033))
end
| uu____4038 -> begin
(

let retc = (return_value env (FStar_Syntax_Util.comp_result c) e)
in (

let uu____4040 = (

let uu____4041 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____4041)))
in (match (uu____4040) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___137_4046 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___137_4046.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___137_4046.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___137_4046.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____4047 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags)
end)))
end))
end
| uu____4048 -> begin
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

let uu____4057 = (

let uu____4060 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____4060 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4057))
in (

let eq1 = (

let uu____4064 = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Util.mk_eq2 uu____4064 t xexp e))
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____4066 = (

let uu____4067 = (

let uu____4072 = (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp c2) ((FStar_Pervasives_Native.Some (x)), (eq_ret)))
in uu____4072.FStar_Syntax_Syntax.comp)
in (uu____4067 ()))
in (FStar_Syntax_Util.comp_set_flags uu____4066 flags))))))))))
end))
end))
end))))
in (

let uu___138_4074 = lc
in {FStar_Syntax_Syntax.eff_name = uu___138_4074.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___138_4074.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine1}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____4097 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____4097) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4102 = (

let uu____4103 = (

let uu____4106 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____4107 = (FStar_TypeChecker_Env.get_range env)
in ((uu____4106), (uu____4107))))
in FStar_Errors.Error (uu____4103))
in (FStar_Pervasives.raise uu____4102))
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____4137 = (

let uu____4138 = (FStar_Syntax_Subst.compress t2)
in uu____4138.FStar_Syntax_Syntax.n)
in (match (uu____4137) with
| FStar_Syntax_Syntax.Tm_type (uu____4141) -> begin
true
end
| uu____4142 -> begin
false
end))))
in (

let uu____4143 = (

let uu____4144 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in uu____4144.FStar_Syntax_Syntax.n)
in (match (uu____4143) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____4150 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let lc1 = (

let uu____4157 = (

let uu____4158 = (

let uu____4159 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4159))
in ((FStar_Pervasives_Native.None), (uu____4158)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____4157))
in (

let e1 = (

let uu____4168 = (

let uu____4169 = (

let uu____4170 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4170)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4169))
in (uu____4168 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____4177 -> begin
((e), (lc))
end))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____4204 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____4204) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____4217 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____4229 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4229), (false)))
end
| uu____4232 -> begin
(

let uu____4233 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4233), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____4239) -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___139_4243 = lc
in {FStar_Syntax_Syntax.eff_name = uu___139_4243.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___139_4243.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___139_4243.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard));
)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____4247 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____4247) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___140_4252 = lc
in {FStar_Syntax_Syntax.eff_name = uu___140_4252.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___140_4252.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___140_4252.FStar_Syntax_Syntax.comp})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___141_4255 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___141_4255.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___141_4255.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___141_4255.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____4261 -> (

let uu____4262 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4262) with
| true -> begin
(lc.FStar_Syntax_Syntax.comp ())
end
| uu____4265 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in (

let uu____4267 = (

let uu____4268 = (FStar_Syntax_Subst.compress f1)
in uu____4268.FStar_Syntax_Syntax.n)
in (match (uu____4267) with
| FStar_Syntax_Syntax.Tm_abs (uu____4273, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4275; FStar_Syntax_Syntax.pos = uu____4276; FStar_Syntax_Syntax.vars = uu____4277}, uu____4278) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___142_4292 = lc
in {FStar_Syntax_Syntax.eff_name = uu___142_4292.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___142_4292.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___142_4292.FStar_Syntax_Syntax.comp})
in (lc1.FStar_Syntax_Syntax.comp ()))
end
| uu____4293 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in ((

let uu____4298 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4298) with
| true -> begin
(

let uu____4299 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____4300 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____4301 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____4302 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____4299 uu____4300 uu____4301 uu____4302)))))
end
| uu____4303 -> begin
()
end));
(

let ct = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4305 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____4305) with
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

let uu____4316 = (destruct_comp ct)
in (match (uu____4316) with
| (u_t, uu____4323, uu____4324) -> begin
(

let wp = (

let uu____4328 = (

let uu____4329 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (

let uu____4330 = (

let uu____4331 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____4332 = (

let uu____4334 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____4334)::[])
in (uu____4331)::uu____4332))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4329 uu____4330)))
in (uu____4328 (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos))
in (

let cret = (

let uu____4340 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4340))
in (

let guard = (match (apply_guard1) with
| true -> begin
(

let uu____4350 = (

let uu____4351 = (

let uu____4352 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____4352)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____4351))
in (uu____4350 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f1.FStar_Syntax_Syntax.pos))
end
| uu____4357 -> begin
f1
end)
in (

let uu____4358 = (

let uu____4361 = (FStar_All.pipe_left (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____4372 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____4373 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____4361 uu____4372 e cret uu____4373))))
in (match (uu____4358) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___143_4379 = x
in {FStar_Syntax_Syntax.ppname = uu___143_4379.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___143_4379.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____4381 = (

let uu____4382 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4382))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____4381 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (c1.FStar_Syntax_Syntax.comp ())
in ((

let uu____4392 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4392) with
| true -> begin
(

let uu____4393 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____4393))
end
| uu____4394 -> begin
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

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___101_4400 -> (match (uu___101_4400) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____4402 -> begin
[]
end))))
in (

let lc1 = (

let uu___144_4404 = lc
in (

let uu____4405 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____4405; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g2 = (

let uu___145_4407 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___145_4407.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___145_4407.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___145_4407.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____4429 = (

let uu____4430 = (

let uu____4431 = (

let uu____4432 = (

let uu____4433 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____4433))
in (uu____4432)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____4431))
in (uu____4430 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____4429))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____4442 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____4442) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____4449 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____4453) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____4462) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____4479))::((ens, uu____4481))::uu____4482 -> begin
(

let uu____4504 = (

let uu____4506 = (norm req)
in FStar_Pervasives_Native.Some (uu____4506))
in (

let uu____4507 = (

let uu____4508 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm uu____4508))
in ((uu____4504), (uu____4507))))
end
| uu____4510 -> begin
(

let uu____4516 = (

let uu____4517 = (

let uu____4520 = (

let uu____4521 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____4521))
in ((uu____4520), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____4517))
in (FStar_Pervasives.raise uu____4516))
end)
end
| uu____4525 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____4531))::uu____4532 -> begin
(

let uu____4546 = (

let uu____4549 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4549))
in (match (uu____4546) with
| (us_r, uu____4566) -> begin
(

let uu____4567 = (

let uu____4570 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4570))
in (match (uu____4567) with
| (us_e, uu____4587) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____4590 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4590 us_r))
in (

let as_ens = (

let uu____4592 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4592 us_e))
in (

let req = (

let uu____4596 = (

let uu____4597 = (

let uu____4598 = (

let uu____4605 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4605)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____4598)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____4597))
in (uu____4596 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____4621 = (

let uu____4622 = (

let uu____4623 = (

let uu____4630 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4630)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____4623)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____4622))
in (uu____4621 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____4643 = (

let uu____4645 = (norm req)
in FStar_Pervasives_Native.Some (uu____4645))
in (

let uu____4646 = (

let uu____4647 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm uu____4647))
in ((uu____4643), (uu____4646)))))))))
end))
end))
end
| uu____4649 -> begin
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

let uu____4671 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____4671) with
| true -> begin
(

let uu____4672 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____4673 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____4672 uu____4673)))
end
| uu____4674 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____4697 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____4697) with
| true -> begin
(

let uu____4698 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____4699 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____4698 uu____4699)))
end
| uu____4700 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____4705 = (

let uu____4706 = (

let uu____4707 = (FStar_Syntax_Subst.compress t)
in uu____4707.FStar_Syntax_Syntax.n)
in (match (uu____4706) with
| FStar_Syntax_Syntax.Tm_app (uu____4710) -> begin
false
end
| uu____4720 -> begin
true
end))
in (match (uu____4705) with
| true -> begin
t
end
| uu____4721 -> begin
(

let uu____4722 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4722) with
| (head1, args) -> begin
(

let uu____4748 = (

let uu____4749 = (

let uu____4750 = (FStar_Syntax_Subst.compress head1)
in uu____4750.FStar_Syntax_Syntax.n)
in (match (uu____4749) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____4753 -> begin
false
end))
in (match (uu____4748) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____4769 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____4775 -> begin
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
| uu____4795 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____4800 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____4800) with
| (formals, uu____4809) -> begin
(

let n_implicits = (

let uu____4821 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____4861 -> (match (uu____4861) with
| (uu____4865, imp) -> begin
((imp = FStar_Pervasives_Native.None) || (imp = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)))
end))))
in (match (uu____4821) with
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

let uu____4940 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____4940) with
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

let uu____4961 = (

let uu____4962 = (

let uu____4965 = (

let uu____4966 = (FStar_Util.string_of_int n_expected)
in (

let uu____4973 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____4974 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____4966 uu____4973 uu____4974))))
in (

let uu____4981 = (FStar_TypeChecker_Env.get_range env)
in ((uu____4965), (uu____4981))))
in FStar_Errors.Error (uu____4962))
in (FStar_Pervasives.raise uu____4961))
end
| uu____4983 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___102_4999 -> (match (uu___102_4999) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____5018 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____5018) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_40), uu____5079) when (_0_40 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____5101, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____5120 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____5120) with
| (v1, uu____5141, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____5151 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____5151) with
| (args, bs3, subst3, g') -> begin
(

let uu____5200 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____5200)))
end)))
end)))
end
| (uu____5214, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____5238 = (

let uu____5252 = (inst_n_binders t)
in (aux [] uu____5252 bs1))
in (match (uu____5238) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____5290) -> begin
((e), (torig), (guard))
end
| (uu____5306, []) when (

let uu____5322 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____5322))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____5323 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____5342 -> begin
(FStar_Syntax_Util.arrow bs2 c1)
end)
in (

let t2 = (FStar_Syntax_Subst.subst subst1 t1)
in (

let e1 = (FStar_Syntax_Syntax.mk_Tm_app e args (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((e1), (t2), (guard)))))
end)
end)))
end))
end
| uu____5355 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____5362 = (

let uu____5364 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____5364 (FStar_List.map (fun u -> (

let uu____5371 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____5371 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____5362 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____5385 = (FStar_Util.set_is_empty x)
in (match (uu____5385) with
| true -> begin
[]
end
| uu____5387 -> begin
(

let s = (

let uu____5390 = (

let uu____5392 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____5392))
in (FStar_All.pipe_right uu____5390 FStar_Util.set_elements))
in ((

let uu____5397 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5397) with
| true -> begin
(

let uu____5398 = (

let uu____5399 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____5399))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____5398))
end
| uu____5401 -> begin
()
end));
(

let r = (

let uu____5404 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____5404))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____5416 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5416) with
| true -> begin
(

let uu____5417 = (

let uu____5418 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____5418))
in (

let uu____5419 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____5420 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____5417 uu____5419 uu____5420))))
end
| uu____5421 -> begin
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

let uu____5439 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____5439 FStar_Util.fifo_set_elements))
in univnames1))))


let maybe_set_tk = (fun ts uu___103_5469 -> (match (uu___103_5469) with
| FStar_Pervasives_Native.None -> begin
ts
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let t2 = (FStar_Syntax_Subst.close_univ_vars (FStar_Pervasives_Native.fst ts) t1)
in ((FStar_ST.write (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.tk (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)));
ts;
)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____5512) -> begin
generalized_univ_names
end
| (uu____5516, []) -> begin
explicit_univ_names
end
| uu____5520 -> begin
(

let uu____5525 = (

let uu____5526 = (

let uu____5529 = (

let uu____5530 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____5530))
in ((uu____5529), (t.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____5526))
in (FStar_Pervasives.raise uu____5525))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in (

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____5546 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5546) with
| true -> begin
(

let uu____5547 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____5547))
end
| uu____5548 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____5552 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5552) with
| true -> begin
(

let uu____5553 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" uu____5553))
end
| uu____5554 -> begin
()
end));
(

let univs2 = (check_universe_generalization univnames1 gen1 t0)
in (

let t1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env t)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs2 t1)
in (

let uu____5559 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs2), (ts)) uu____5559)))));
));
)))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list FStar_Pervasives_Native.option = (fun env ecs -> (

let uu____5591 = (

let uu____5592 = (FStar_Util.for_all (fun uu____5600 -> (match (uu____5600) with
| (uu____5605, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation uu____5592))
in (match (uu____5591) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5622 -> begin
(

let norm = (fun c -> ((

let uu____5628 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5628) with
| true -> begin
(

let uu____5629 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____5629))
end
| uu____5630 -> begin
()
end));
(

let c1 = (

let uu____5632 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____5632) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
| uu____5633 -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end))
in ((

let uu____5635 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5635) with
| true -> begin
(

let uu____5636 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5636))
end
| uu____5637 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____5676 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____5676 FStar_Util.set_elements)))
in (

let uu____5730 = (

let uu____5750 = (FStar_All.pipe_right ecs (FStar_List.map (fun uu____5823 -> (match (uu____5823) with
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
in ((

let uu____5865 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5865) with
| true -> begin
(

let uu____5866 = (

let uu____5867 = (

let uu____5869 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____5869 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____5867 (FStar_String.concat ", ")))
in (

let uu____5884 = (

let uu____5885 = (

let uu____5887 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____5887 (FStar_List.map (fun uu____5904 -> (match (uu____5904) with
| (u, t2) -> begin
(

let uu____5909 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____5910 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s : %s)" uu____5909 uu____5910)))
end)))))
in (FStar_All.pipe_right uu____5885 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____5866 uu____5884)))
end
| uu____5912 -> begin
()
end));
(

let univs2 = (

let uu____5915 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uu____5930 -> (match (uu____5930) with
| (uu____5935, t2) -> begin
(

let uu____5937 = (FStar_Syntax_Free.univs t2)
in (FStar_Util.set_union univs2 uu____5937))
end)) univs1 uu____5915))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____5952 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5952) with
| true -> begin
(

let uu____5953 = (

let uu____5954 = (

let uu____5956 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____5956 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____5954 (FStar_String.concat ", ")))
in (

let uu____5971 = (

let uu____5972 = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____5993 -> (match (uu____5993) with
| (u, t2) -> begin
(

let uu____5998 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____5999 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s : %s)" uu____5998 uu____5999)))
end))))
in (FStar_All.pipe_right uu____5972 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____5953 uu____5971)))
end
| uu____6001 -> begin
()
end));
((univs2), (((uvs), (e), (c1))));
)));
))))))
end))))
in (FStar_All.pipe_right uu____5750 FStar_List.unzip))
in (match (uu____5730) with
| (univs1, uvars1) -> begin
(

let univs2 = (

let uu____6124 = (FStar_List.hd univs1)
in (

let uu____6127 = (FStar_List.tl univs1)
in (FStar_List.fold_left (fun out u -> (

let uu____6140 = ((FStar_Util.set_is_subset_of out u) && (FStar_Util.set_is_subset_of u out))
in (match (uu____6140) with
| true -> begin
out
end
| uu____6142 -> begin
(

let uu____6143 = (

let uu____6144 = (

let uu____6147 = (FStar_TypeChecker_Env.get_range env)
in (("Generalizing the types of these mutually recursive definitions requires an incompatible set of universes"), (uu____6147)))
in FStar_Errors.Error (uu____6144))
in (FStar_Pervasives.raise uu____6143))
end))) uu____6124 uu____6127)))
in (

let gen_univs1 = (gen_univs env univs2)
in ((

let uu____6152 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____6152) with
| true -> begin
(FStar_All.pipe_right gen_univs1 (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end
| uu____6156 -> begin
()
end));
(

let ecs1 = (FStar_All.pipe_right uvars1 (FStar_List.map (fun uu____6201 -> (match (uu____6201) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____6246 -> (match (uu____6246) with
| (u, k) -> begin
(

let uu____6254 = (FStar_Syntax_Unionfind.find u)
in (match (uu____6254) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = uu____6260; FStar_Syntax_Syntax.pos = uu____6261; FStar_Syntax_Syntax.vars = uu____6262}) -> begin
((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (uu____6268, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = uu____6270; FStar_Syntax_Syntax.pos = uu____6271; FStar_Syntax_Syntax.vars = uu____6272}, uu____6273); FStar_Syntax_Syntax.tk = uu____6274; FStar_Syntax_Syntax.pos = uu____6275; FStar_Syntax_Syntax.vars = uu____6276}) -> begin
((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Pervasives_Native.Some (uu____6294) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____6298 -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let uu____6301 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____6301) with
| (bs, kres) -> begin
(

let a = (

let uu____6325 = (

let uu____6327 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____6327))
in (FStar_Syntax_Syntax.new_bv uu____6325 kres))
in (

let t = (

let uu____6330 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____6330 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
in ((FStar_Syntax_Util.set_uvar u t);
((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)));
)))
end)))
end))
end))))
in (

let uu____6333 = (match (((tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c))
end
| uu____6351 -> begin
(

let uu____6359 = ((e), (c))
in (match (uu____6359) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let t = (

let uu____6371 = (

let uu____6372 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____6372.FStar_Syntax_Syntax.n)
in (match (uu____6371) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____6389 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____6389) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs1) cod1)
end))
end
| uu____6399 -> begin
(FStar_Syntax_Util.arrow tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs tvars e1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____6401 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____6401)))))))
end))
end)
in (match (uu____6333) with
| (e1, c1) -> begin
((gen_univs1), (e1), (c1))
end)))
end))))
in FStar_Pervasives_Native.Some (ecs1));
)))
end)))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> ((

let uu____6441 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6441) with
| true -> begin
(

let uu____6442 = (

let uu____6443 = (FStar_List.map (fun uu____6452 -> (match (uu____6452) with
| (lb, uu____6457, uu____6458) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____6443 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____6442))
end
| uu____6460 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____6472 -> (match (uu____6472) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____6487 = (

let uu____6494 = (FStar_All.pipe_right lecs (FStar_List.map (fun uu____6514 -> (match (uu____6514) with
| (uu____6520, e, c) -> begin
((e), (c))
end))))
in (gen env uu____6494))
in (match (uu____6487) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____6556 -> (match (uu____6556) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| FStar_Pervasives_Native.Some (ecs) -> begin
(FStar_List.map2 (fun uu____6609 uu____6610 -> (match (((uu____6609), (uu____6610))) with
| ((l, uu____6643, uu____6644), (us, e, c)) -> begin
((

let uu____6670 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____6670) with
| true -> begin
(

let uu____6671 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____6672 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____6673 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____6674 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" uu____6671 uu____6672 uu____6673 uu____6674)))))
end
| uu____6675 -> begin
()
end));
((l), (us), (e), (c));
)
end)) lecs ecs)
end))
in (FStar_List.map2 (fun univnames1 uu____6700 -> (match (uu____6700) with
| (l, generalized_univs, t, c) -> begin
(

let uu____6718 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____6718), (t), (c)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____6754 -> begin
(

let uu____6755 = (FStar_TypeChecker_Rel.try_subtype env2 t11 t21)
in (match (uu____6755) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____6759 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____6759))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____6765 = (

let uu____6766 = (FStar_Syntax_Subst.compress e1)
in uu____6766.FStar_Syntax_Syntax.n)
in (match (uu____6765) with
| FStar_Syntax_Syntax.Tm_name (uu____6769) -> begin
true
end
| uu____6770 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___146_6790 = x
in {FStar_Syntax_Syntax.ppname = uu___146_6790.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___146_6790.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) e2.FStar_Syntax_Syntax.pos)
end
| uu____6791 -> begin
(

let uu___147_6792 = e2
in (

let uu____6793 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = uu___147_6792.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu____6793; FStar_Syntax_Syntax.pos = uu___147_6792.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___147_6792.FStar_Syntax_Syntax.vars}))
end)))
in (

let env2 = (

let uu___148_6802 = env1
in (

let uu____6803 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___148_6802.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___148_6802.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___148_6802.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___148_6802.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___148_6802.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___148_6802.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___148_6802.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___148_6802.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___148_6802.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___148_6802.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___148_6802.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___148_6802.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___148_6802.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___148_6802.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___148_6802.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____6803; FStar_TypeChecker_Env.is_iface = uu___148_6802.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___148_6802.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___148_6802.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___148_6802.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___148_6802.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___148_6802.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___148_6802.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___148_6802.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___148_6802.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___148_6802.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___148_6802.FStar_TypeChecker_Env.is_native_tactic}))
in (

let uu____6804 = (check env2 t1 t2)
in (match (uu____6804) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6808 = (

let uu____6809 = (

let uu____6812 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____6813 = (FStar_TypeChecker_Env.get_range env2)
in ((uu____6812), (uu____6813))))
in FStar_Errors.Error (uu____6809))
in (FStar_Pervasives.raise uu____6808))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____6818 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____6818) with
| true -> begin
(

let uu____6819 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____6819))
end
| uu____6820 -> begin
()
end));
(

let uu____6821 = (decorate e t2)
in ((uu____6821), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____6848 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____6848) with
| true -> begin
(

let uu____6851 = (discharge g1)
in (

let uu____6852 = (lc.FStar_Syntax_Syntax.comp ())
in ((uu____6851), (uu____6852))))
end
| uu____6857 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c1 = (

let uu____6864 = (

let uu____6865 = (

let uu____6866 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____6866 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____6865 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____6864 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____6868 = (destruct_comp c1)
in (match (uu____6868) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____6880 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____6881 = (

let uu____6882 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____6883 = (

let uu____6884 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6885 = (

let uu____6887 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6887)::[])
in (uu____6884)::uu____6885))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6882 uu____6883)))
in (uu____6881 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) uu____6880)))
in ((

let uu____6893 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____6893) with
| true -> begin
(

let uu____6894 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____6894))
end
| uu____6895 -> begin
()
end));
(

let g2 = (

let uu____6897 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____6897))
in (

let uu____6898 = (discharge g2)
in (

let uu____6899 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____6898), (uu____6899)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___104_6925 -> (match (uu___104_6925) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____6931))::[] -> begin
(f fst1)
end
| uu____6944 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____6949 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____6949 (fun _0_43 -> FStar_TypeChecker_Common.NonTrivial (_0_43)))))
in (

let op_or_e = (fun e -> (

let uu____6958 = (

let uu____6961 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____6961))
in (FStar_All.pipe_right uu____6958 (fun _0_44 -> FStar_TypeChecker_Common.NonTrivial (_0_44)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_45 -> FStar_TypeChecker_Common.NonTrivial (_0_45))))
in (

let op_or_t = (fun t -> (

let uu____6972 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____6972 (fun _0_46 -> FStar_TypeChecker_Common.NonTrivial (_0_46)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_47 -> FStar_TypeChecker_Common.NonTrivial (_0_47))))
in (

let short_op_ite = (fun uu___105_6986 -> (match (uu___105_6986) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____6992))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____7007))::[] -> begin
(

let uu____7028 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____7028 (fun _0_48 -> FStar_TypeChecker_Common.NonTrivial (_0_48))))
end
| uu____7033 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____7040 = (

let uu____7045 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____7045)))
in (

let uu____7050 = (

let uu____7056 = (

let uu____7061 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____7061)))
in (

let uu____7066 = (

let uu____7072 = (

let uu____7077 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____7077)))
in (

let uu____7082 = (

let uu____7088 = (

let uu____7093 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____7093)))
in (

let uu____7098 = (

let uu____7104 = (

let uu____7109 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____7109)))
in (uu____7104)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____7088)::uu____7098))
in (uu____7072)::uu____7082))
in (uu____7056)::uu____7066))
in (uu____7040)::uu____7050))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____7146 = (FStar_Util.find_map table (fun uu____7156 -> (match (uu____7156) with
| (x, mk1) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
(

let uu____7169 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____7169))
end
| uu____7170 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (uu____7146) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____7172 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____7177 = (

let uu____7178 = (FStar_Syntax_Util.un_uinst l)
in uu____7178.FStar_Syntax_Syntax.n)
in (match (uu____7177) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____7182 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____7202))::uu____7203 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____7209 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____7213, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7214))))::uu____7215 -> begin
bs
end
| uu____7224 -> begin
(

let uu____7225 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____7225) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____7228 = (

let uu____7229 = (FStar_Syntax_Subst.compress t)
in uu____7229.FStar_Syntax_Syntax.n)
in (match (uu____7228) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____7233) -> begin
(

let uu____7244 = (FStar_Util.prefix_until (fun uu___106_7266 -> (match (uu___106_7266) with
| (uu____7270, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7271))) -> begin
false
end
| uu____7273 -> begin
true
end)) bs')
in (match (uu____7244) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____7291, uu____7292) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____7329, uu____7330) -> begin
(

let uu____7367 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____7378 -> (match (uu____7378) with
| (x, uu____7383) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____7367) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____7410 -> (match (uu____7410) with
| (x, i) -> begin
(

let uu____7421 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____7421), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____7426 -> begin
bs
end))
end))
end
| uu____7427 -> begin
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
| uu____7450 -> begin
(

let uu____7451 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) uu____7451 e.FStar_Syntax_Syntax.pos))
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____7477 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____7477) with
| true -> begin
e
end
| uu____7478 -> begin
(

let uu____7479 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) uu____7479 e.FStar_Syntax_Syntax.pos))
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____7509 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____7509) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(

let uu____7511 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) uu____7511));
)
end
| uu____7512 -> begin
()
end));
(

let fv = (

let uu____7514 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____7514 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[]), ([])))))
in (

let uu____7521 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___149_7531 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___149_7531.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___149_7531.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___149_7531.FStar_Syntax_Syntax.sigmeta})), (uu____7521)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___107_7543 -> (match (uu___107_7543) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7544 -> begin
false
end))
in (

let reducibility = (fun uu___108_7548 -> (match (uu___108_7548) with
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
| uu____7549 -> begin
false
end))
in (

let assumption = (fun uu___109_7553 -> (match (uu___109_7553) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____7554 -> begin
false
end))
in (

let reification = (fun uu___110_7558 -> (match (uu___110_7558) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____7559) -> begin
true
end
| uu____7560 -> begin
false
end))
in (

let inferred = (fun uu___111_7564 -> (match (uu___111_7564) with
| FStar_Syntax_Syntax.Discriminator (uu____7565) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____7566) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____7569) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____7574) -> begin
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
| uu____7579 -> begin
false
end))
in (

let has_eq = (fun uu___112_7583 -> (match (uu___112_7583) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____7584 -> begin
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
| FStar_Syntax_Syntax.Reflectable (uu____7630) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (x = FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7634 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____7637 = (

let uu____7638 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___113_7641 -> (match (uu___113_7641) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____7642 -> begin
false
end))))
in (FStar_All.pipe_right uu____7638 Prims.op_Negation))
in (match (uu____7637) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (

let uu____7654 = (

let uu____7655 = (

let uu____7658 = (

let uu____7659 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____7659 msg))
in ((uu____7658), (r)))
in FStar_Errors.Error (uu____7655))
in (FStar_Pervasives.raise uu____7654)))
in (

let err1 = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____7667 -> (err' ""))
in ((match (((FStar_List.length quals) <> (FStar_List.length no_dup_quals))) with
| true -> begin
(err1 "duplicate qualifiers")
end
| uu____7677 -> begin
()
end);
(

let uu____7679 = (

let uu____7680 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____7680)))
in (match (uu____7679) with
| true -> begin
(err1 "ill-formed combination")
end
| uu____7682 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7684), uu____7685, uu____7686) -> begin
((

let uu____7697 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____7697) with
| true -> begin
(err1 "recursive definitions cannot be marked inline")
end
| uu____7699 -> begin
()
end));
(

let uu____7700 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____7700) with
| true -> begin
(err1 "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____7704 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____7705) -> begin
(

let uu____7710 = (

let uu____7711 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____7711)))
in (match (uu____7710) with
| true -> begin
(err'1 ())
end
| uu____7715 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____7716) -> begin
(

let uu____7720 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____7720) with
| true -> begin
(err'1 ())
end
| uu____7722 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____7723) -> begin
(

let uu____7727 = (

let uu____7728 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption)))))
in (not (uu____7728)))
in (match (uu____7727) with
| true -> begin
(err'1 ())
end
| uu____7732 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____7733) -> begin
(

let uu____7734 = (

let uu____7735 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____7735)))
in (match (uu____7734) with
| true -> begin
(err'1 ())
end
| uu____7739 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____7740) -> begin
(

let uu____7741 = (

let uu____7742 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____7742)))
in (match (uu____7741) with
| true -> begin
(err'1 ())
end
| uu____7746 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7747) -> begin
(

let uu____7754 = (

let uu____7755 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____7755)))
in (match (uu____7754) with
| true -> begin
(err'1 ())
end
| uu____7759 -> begin
()
end))
end
| uu____7760 -> begin
()
end);
))))))
end
| uu____7761 -> begin
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

let uu____7827 = (

let uu____7830 = (

let uu____7831 = (

let uu____7836 = (

let uu____7837 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7837))
in ((uu____7836), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____7831))
in (FStar_Syntax_Syntax.mk uu____7830))
in (uu____7827 FStar_Pervasives_Native.None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7867 -> (match (uu____7867) with
| (x, imp) -> begin
(

let uu____7874 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7874), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args FStar_Pervasives_Native.None p)))
in (

let unrefined_arg_binder = (

let uu____7878 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____7878))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____7880 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____7887 = (

let uu____7888 = (

let uu____7889 = (

let uu____7890 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____7891 = (

let uu____7892 = (

let uu____7893 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7893))
in (uu____7892)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____7890 uu____7891)))
in (uu____7889 FStar_Pervasives_Native.None p))
in (FStar_Syntax_Util.b2t uu____7888))
in (FStar_Syntax_Util.refine x uu____7887)))
in (

let uu____7898 = (

let uu___150_7899 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___150_7899.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_7899.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____7898)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____7910 = (FStar_List.map (fun uu____7923 -> (match (uu____7923) with
| (x, uu____7930) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____7910 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7957 -> (match (uu____7957) with
| (x, uu____7964) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((fvq <> FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____7969 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((

let uu____7975 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____7975)) || (

let uu____7977 = (

let uu____7978 = (FStar_TypeChecker_Env.current_module env)
in uu____7978.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____7977)))
in (

let quals = (

let uu____7981 = (

let uu____7983 = (

let uu____7985 = (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit))
in (match (uu____7985) with
| true -> begin
(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____7987 -> begin
[]
end))
in (

let uu____7988 = (FStar_List.filter (fun uu___114_7991 -> (match (uu___114_7991) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7992 -> begin
false
end)) iquals)
in (FStar_List.append uu____7983 uu____7988)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::[]
end
| uu____7994 -> begin
[]
end)) uu____7981))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____8005 = (

let uu____8006 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____8006))
in (FStar_Syntax_Syntax.mk_Total uu____8005))
in (

let uu____8007 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____8007)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid discriminator_name); FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta}
in ((

let uu____8010 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8010) with
| true -> begin
(

let uu____8011 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____8011))
end
| uu____8012 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____8014 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____8020 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____8046 -> (match (uu____8046) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____8062 = (

let uu____8064 = (

let uu____8065 = (

let uu____8070 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____8070), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____8065))
in (pos uu____8064))
in ((uu____8062), (b)))
end
| uu____8072 -> begin
(

let uu____8073 = (

let uu____8075 = (

let uu____8076 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8076))
in (pos uu____8075))
in ((uu____8073), (b)))
end))
end))))
in (

let pat_true = (

let uu____8088 = (

let uu____8090 = (

let uu____8091 = (

let uu____8098 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____8098), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____8091))
in (pos uu____8090))
in ((uu____8088), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_true_bool)))
in (

let pat_false = (

let uu____8121 = (

let uu____8123 = (

let uu____8124 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8124))
in (pos uu____8123))
in ((uu____8121), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst unrefined_arg_binder))
in (

let uu____8134 = (

let uu____8137 = (

let uu____8138 = (

let uu____8153 = (

let uu____8155 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____8156 = (

let uu____8158 = (FStar_Syntax_Util.branch pat_false)
in (uu____8158)::[])
in (uu____8155)::uu____8156))
in ((arg_exp), (uu____8153)))
in FStar_Syntax_Syntax.Tm_match (uu____8138))
in (FStar_Syntax_Syntax.mk uu____8137))
in (uu____8134 FStar_Pervasives_Native.None p))))))
end)
in (

let dd = (

let uu____8169 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____8169) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____8171 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____8174 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____8176 = (

let uu____8179 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____8179))
in (

let uu____8180 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____8176; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____8180}))
in (

let impl = (

let uu____8184 = (

let uu____8185 = (

let uu____8191 = (

let uu____8193 = (

let uu____8194 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____8194 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____8193)::[])
in ((((false), ((lb)::[]))), (uu____8191), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____8185))
in {FStar_Syntax_Syntax.sigel = uu____8184; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta})
in ((

let uu____8206 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8206) with
| true -> begin
(

let uu____8207 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____8207))
end
| uu____8208 -> begin
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

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____8236 -> (match (uu____8236) with
| (a, uu____8240) -> begin
(

let uu____8241 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____8241) with
| (field_name, uu____8245) -> begin
(

let field_proj_tm = (

let uu____8247 = (

let uu____8248 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____8248))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8247 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) FStar_Pervasives_Native.None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____8262 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____8286 -> (match (uu____8286) with
| (x, uu____8291) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____8293 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____8293) with
| (field_name, uu____8298) -> begin
(

let t = (

let uu____8300 = (

let uu____8301 = (

let uu____8304 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____8304))
in (FStar_Syntax_Util.arrow binders uu____8301))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____8300))
in (

let only_decl = ((

let uu____8308 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____8308)) || (

let uu____8310 = (

let uu____8311 = (FStar_TypeChecker_Env.current_module env)
in uu____8311.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____8310)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____8321 = (FStar_List.filter (fun uu___115_8324 -> (match (uu___115_8324) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____8325 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____8321)
end
| uu____8326 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___116_8334 -> (match (uu___116_8334) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____8335 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta}
in ((

let uu____8338 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8338) with
| true -> begin
(

let uu____8339 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____8339))
end
| uu____8340 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____8342 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____8369 -> (match (uu____8369) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match (((i + ntps) = j)) with
| true -> begin
(

let uu____8385 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____8385), (b)))
end
| uu____8388 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____8396 = (

let uu____8398 = (

let uu____8399 = (

let uu____8404 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____8404), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____8399))
in (pos uu____8398))
in ((uu____8396), (b)))
end
| uu____8406 -> begin
(

let uu____8407 = (

let uu____8409 = (

let uu____8410 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8410))
in (pos uu____8409))
in ((uu____8407), (b)))
end)
end))
end))))
in (

let pat = (

let uu____8420 = (

let uu____8422 = (

let uu____8423 = (

let uu____8430 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____8430), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____8423))
in (pos uu____8422))
in (

let uu____8435 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____8420), (FStar_Pervasives_Native.None), (uu____8435))))
in (

let body = (

let uu____8445 = (

let uu____8448 = (

let uu____8449 = (

let uu____8464 = (

let uu____8466 = (FStar_Syntax_Util.branch pat)
in (uu____8466)::[])
in ((arg_exp), (uu____8464)))
in FStar_Syntax_Syntax.Tm_match (uu____8449))
in (FStar_Syntax_Syntax.mk uu____8448))
in (uu____8445 FStar_Pervasives_Native.None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let dd = (

let uu____8478 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____8478) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____8480 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____8482 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____8484 = (

let uu____8487 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____8487))
in (

let uu____8488 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____8484; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____8488}))
in (

let impl = (

let uu____8492 = (

let uu____8493 = (

let uu____8499 = (

let uu____8501 = (

let uu____8502 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____8502 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____8501)::[])
in ((((false), ((lb)::[]))), (uu____8499), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____8493))
in {FStar_Syntax_Syntax.sigel = uu____8492; FStar_Syntax_Syntax.sigrng = p1; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta})
in ((

let uu____8514 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8514) with
| true -> begin
(

let uu____8515 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____8515))
end
| uu____8516 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____8518 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
)))))))
end)))
end))))
in (FStar_All.pipe_right uu____8262 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, uu____8549) when (not ((FStar_Ident.lid_equals constr_lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____8552 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____8552) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____8565 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____8565) with
| (formals, uu____8575) -> begin
(

let uu____8586 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____8608 = (

let uu____8609 = (

let uu____8610 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____8610))
in (FStar_Ident.lid_equals typ_lid uu____8609))
in (match (uu____8608) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____8620, uvs', tps, typ0, uu____8624, constrs) -> begin
FStar_Pervasives_Native.Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____8641 -> begin
(failwith "Impossible")
end)
end
| uu____8646 -> begin
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
| uu____8673 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____8586) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____8683 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____8683) with
| (indices, uu____8693) -> begin
(

let refine_domain = (

let uu____8705 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___117_8709 -> (match (uu___117_8709) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8710) -> begin
true
end
| uu____8715 -> begin
false
end))))
in (match (uu____8705) with
| true -> begin
false
end
| uu____8716 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___118_8722 -> (match (uu___118_8722) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8724, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____8731 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____8732 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____8732) with
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
| uu____8738 -> begin
iquals
end)
in (

let fields = (

let uu____8740 = (FStar_Util.first_N n_typars formals)
in (match (uu____8740) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____8778 uu____8779 -> (match (((uu____8778), (uu____8779))) with
| ((x, uu____8789), (x', uu____8791)) -> begin
(

let uu____8796 = (

let uu____8801 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____8801)))
in FStar_Syntax_Syntax.NT (uu____8796))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____8802 -> begin
[]
end))




