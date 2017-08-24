
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (

let uu____12 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____13 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.err uu____12 uu____13))))


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
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____50)))
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
in (FStar_Pervasives_Native.fst uu____59)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___97_64 -> (match (uu___97_64) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, uu____66); FStar_Syntax_Syntax.tk = uu____67; FStar_Syntax_Syntax.pos = uu____68; FStar_Syntax_Syntax.vars = uu____69} -> begin
uv
end
| uu____84 -> begin
(failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (

let uu____103 = (FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid)
in (match (uu____103) with
| FStar_Pervasives_Native.Some ((uu____116)::((tm, uu____118))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| uu____158 -> begin
(

let uu____165 = (new_uvar_aux env k)
in (match (uu____165) with
| (t, u) -> begin
(

let g = (

let uu___117_177 = FStar_TypeChecker_Rel.trivial_guard
in (

let uu____178 = (

let uu____186 = (

let uu____193 = (as_uvar u)
in ((reason), (env), (uu____193), (t), (k), (r)))
in (uu____186)::[])
in {FStar_TypeChecker_Env.guard_f = uu___117_177.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___117_177.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___117_177.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____178}))
in (

let uu____206 = (

let uu____210 = (

let uu____213 = (as_uvar u)
in ((uu____213), (r)))
in (uu____210)::[])
in ((t), (uu____206), (g))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____231 = (

let uu____232 = (FStar_Util.set_is_empty uvs)
in (not (uu____232)))
in (match (uu____231) with
| true -> begin
(

let us = (

let uu____236 = (

let uu____238 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun uu____254 -> (match (uu____254) with
| (x, uu____262) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) uu____238))
in (FStar_All.pipe_right uu____236 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____279 = (

let uu____280 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____280))
in (FStar_Errors.err r uu____279));
(FStar_Options.pop ());
))
end
| uu____281 -> begin
()
end))))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (

let uu____289 = (FStar_ST.read s.FStar_Syntax_Syntax.tk)
in (match (uu____289) with
| FStar_Pervasives_Native.None -> begin
(

let uu____294 = (

let uu____295 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (

let uu____296 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" uu____295 uu____296)))
in (failwith uu____294))
end
| FStar_Pervasives_Native.Some (tk) -> begin
tk
end)))


let force_sort = (fun s -> (

let uu____311 = (

let uu____314 = (force_sort' s)
in (FStar_Syntax_Syntax.mk uu____314))
in (uu____311 FStar_Pervasives_Native.None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____331 -> (match (uu____331) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____338; FStar_Syntax_Syntax.lbdef = e} -> begin
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
| uu____359 -> begin
()
end);
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder1 = (fun scope a -> (

let uu____370 = (

let uu____371 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in uu____371.FStar_Syntax_Syntax.n)
in (match (uu____370) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____376 = (FStar_Syntax_Util.type_u ())
in (match (uu____376) with
| (k, uu____382) -> begin
(

let t2 = (

let uu____384 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right uu____384 FStar_Pervasives_Native.fst))
in (((

let uu___118_389 = a
in {FStar_Syntax_Syntax.ppname = uu___118_389.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_389.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (false)))
end))
end
| uu____390 -> begin
((a), (true))
end)))
in (

let rec aux = (fun must_check_ty vars e1 -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e3, uu____415) -> begin
(aux must_check_ty vars e3)
end
| FStar_Syntax_Syntax.Tm_ascribed (e3, t2, uu____422) -> begin
(((FStar_Pervasives_Native.fst t2)), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____468) -> begin
(

let uu____491 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____515 uu____516 -> (match (((uu____515), (uu____516))) with
| ((scope, bs1, must_check_ty1), (a, imp)) -> begin
(

let uu____558 = (match (must_check_ty1) with
| true -> begin
((a), (true))
end
| uu____563 -> begin
(mk_binder1 scope a)
end)
in (match (uu____558) with
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
in (match (uu____491) with
| (scope, bs1, must_check_ty1) -> begin
(

let uu____619 = (aux must_check_ty1 scope body)
in (match (uu____619) with
| (res, must_check_ty2) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____636 = (FStar_Options.ml_ish ())
in (match (uu____636) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____637 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Util.arrow bs1 c)
in ((

let uu____643 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____643) with
| true -> begin
(

let uu____644 = (FStar_Range.string_of_range r)
in (

let uu____645 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____646 = (FStar_Util.string_of_bool must_check_ty2)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" uu____644 uu____645 uu____646))))
end
| uu____647 -> begin
()
end));
((FStar_Util.Inl (t2)), (must_check_ty2));
)))
end))
end))
end
| uu____654 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end
| uu____661 -> begin
(

let uu____662 = (

let uu____665 = (

let uu____666 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____666 FStar_Pervasives_Native.fst))
in FStar_Util.Inl (uu____665))
in ((uu____662), (false)))
end)
end)))
in (

let uu____673 = (

let uu____678 = (t_binders env)
in (aux false uu____678 e))
in (match (uu____673) with
| (t2, b) -> begin
(

let t3 = (match (t2) with
| FStar_Util.Inr (c) -> begin
(

let uu____695 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____695) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____698 -> begin
(

let uu____699 = (

let uu____700 = (

let uu____703 = (

let uu____704 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____704))
in ((uu____703), (rng)))
in FStar_Errors.Error (uu____700))
in (FStar_Pervasives.raise uu____699))
end))
end
| FStar_Util.Inl (t3) -> begin
t3
end)
in (([]), (t3), (b)))
end)))));
)
end
| uu____711 -> begin
(

let uu____712 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____712) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let pat_as_exp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c))) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (([]), ([]), ([]), (env1), (e), (p1)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____793) -> begin
(

let uu____798 = (FStar_Syntax_Util.type_u ())
in (match (uu____798) with
| (k, uu____811) -> begin
(

let t = (new_uvar env1 k)
in (

let x1 = (

let uu___119_814 = x
in {FStar_Syntax_Syntax.ppname = uu___119_814.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_814.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____815 = (

let uu____818 = (FStar_TypeChecker_Env.all_binders env1)
in (FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p uu____818 t))
in (match (uu____815) with
| (e, u) -> begin
(

let p2 = (

let uu___120_833 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.ty = uu___120_833.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___120_833.FStar_Syntax_Syntax.p})
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

let uu___121_855 = x
in (

let uu____856 = (new_uvar env1 t)
in {FStar_Syntax_Syntax.ppname = uu___121_855.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_855.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____856}))
in (

let env2 = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env1 x1)
end
| uu____860 -> begin
env1
end)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1))) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (p1)))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____878 = (FStar_Syntax_Util.type_u ())
in (match (uu____878) with
| (t, uu____891) -> begin
(

let x1 = (

let uu___122_893 = x
in (

let uu____894 = (new_uvar env1 t)
in {FStar_Syntax_Syntax.ppname = uu___122_893.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___122_893.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____894}))
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x1)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1))) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ((x1)::[]), ([]), (env2), (e), (p1)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____926 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____982 uu____983 -> (match (((uu____982), (uu____983))) with
| ((b, a, w, env2, args, pats1), (p2, imp)) -> begin
(

let uu____1082 = (pat_as_arg_with_env allow_wc_dependence env2 p2)
in (match (uu____1082) with
| (b', a', w', env3, te, pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1121 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), ((((pat), (imp)))::pats1)))
end))
end)) (([]), ([]), ([]), (env1), ([]), ([]))))
in (match (uu____926) with
| (b, a, w, env2, args, pats1) -> begin
(

let e = (

let uu____1190 = (

let uu____1193 = (

let uu____1194 = (

let uu____1199 = (

let uu____1202 = (

let uu____1203 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____1204 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____1203 uu____1204)))
in (uu____1202 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in ((uu____1199), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____1194))
in (FStar_Syntax_Syntax.mk uu____1193))
in (uu____1190 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in (

let uu____1221 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____1227 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____1233 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____1221), (uu____1227), (uu____1233), (env2), (e), ((

let uu___123_1246 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.ty = uu___123_1246.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___123_1246.FStar_Syntax_Syntax.p})))))))
end))
end))
in (

let rec elaborate_pat = (fun env1 p1 -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end
| uu____1279 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end))
in (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____1308 -> (match (uu____1308) with
| (p2, imp) -> begin
(

let uu____1323 = (elaborate_pat env1 p2)
in ((uu____1323), (imp)))
end)) pats)
in (

let uu____1328 = (FStar_TypeChecker_Env.lookup_datacon env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1328) with
| (uu____1337, t) -> begin
(

let uu____1339 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1339) with
| (f, uu____1350) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____1425)::uu____1426) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((uu____1461)::uu____1462, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____1502 -> (match (uu____1502) with
| (t1, imp) -> begin
(match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____1520 = (

let uu____1522 = (FStar_Syntax_Syntax.range_of_bv t1)
in FStar_Pervasives_Native.Some (uu____1522))
in (FStar_Syntax_Syntax.new_bv uu____1520 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____1528 = (maybe_dot inaccessible a r)
in ((uu____1528), (true)))))
end
| uu____1533 -> begin
(

let uu____1535 = (

let uu____1536 = (

let uu____1539 = (

let uu____1540 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____1540))
in ((uu____1539), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Errors.Error (uu____1536))
in (FStar_Pervasives.raise uu____1535))
end)
end))))
end
| ((f1)::formals', ((p2, p_imp))::pats') -> begin
(match (f1) with
| (uu____1591, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1592))) when p_imp -> begin
(

let uu____1594 = (aux formals' pats')
in (((p2), (true)))::uu____1594)
end
| (uu____1606, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p2.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p3 = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (

let uu____1617 = (aux formals' pats2)
in (((p3), (true)))::uu____1617)))
end
| (uu____1629, imp) -> begin
(

let uu____1633 = (

let uu____1638 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p2), (uu____1638)))
in (

let uu____1641 = (aux formals' pats')
in (uu____1633)::uu____1641))
end)
end))
in (

let uu___124_1651 = p1
in (

let uu____1654 = (

let uu____1655 = (

let uu____1663 = (aux f pats1)
in ((fv), (uu____1663)))
in FStar_Syntax_Syntax.Pat_cons (uu____1655))
in {FStar_Syntax_Syntax.v = uu____1654; FStar_Syntax_Syntax.ty = uu___124_1651.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___124_1651.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____1674 -> begin
p1
end)))
in (

let one_pat = (fun allow_wc_dependence env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____1700 = (pat_as_arg_with_env allow_wc_dependence env1 p2)
in (match (uu____1700) with
| (b, a, w, env2, arg, p3) -> begin
(

let uu____1730 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____1730) with
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____1743 = (

let uu____1744 = (

let uu____1747 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in ((uu____1747), (p3.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____1744))
in (FStar_Pervasives.raise uu____1743))
end
| uu____1756 -> begin
((b), (a), (w), (arg), (p3))
end))
end))))
in (

let uu____1761 = (one_pat true env p)
in (match (uu____1761) with
| (b, uu____1775, uu____1776, tm, p1) -> begin
((b), (tm), (p1))
end))))))


let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.pat = (fun env p exp -> (

let qq = p
in (

let rec aux = (fun p1 e -> (

let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p1.FStar_Syntax_Syntax.p))
in (

let e1 = (FStar_Syntax_Util.unmeta e)
in (match (((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n))) with
| (uu____1817, FStar_Syntax_Syntax.Tm_uinst (e2, uu____1819)) -> begin
(aux p1 e2)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____1824), FStar_Syntax_Syntax.Tm_constant (uu____1825)) -> begin
(

let uu____1826 = (force_sort' e1)
in (pkg p1.FStar_Syntax_Syntax.v uu____1826))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____1830 = (

let uu____1831 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1832 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____1831 uu____1832)))
in (failwith uu____1830))
end
| uu____1833 -> begin
()
end);
(

let uu____1835 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____1835) with
| true -> begin
(

let uu____1836 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1837 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____1836 uu____1837)))
end
| uu____1838 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___125_1841 = x
in {FStar_Syntax_Syntax.ppname = uu___125_1841.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___125_1841.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x1)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____1845 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____1845) with
| true -> begin
(

let uu____1846 = (

let uu____1847 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1848 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____1847 uu____1848)))
in (failwith uu____1846))
end
| uu____1849 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___126_1852 = x
in {FStar_Syntax_Syntax.ppname = uu___126_1852.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___126_1852.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x1)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____1854), uu____1855) -> begin
(

let s = (force_sort e1)
in (

let x1 = (

let uu___127_1864 = x
in {FStar_Syntax_Syntax.ppname = uu___127_1864.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_1864.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x1), (e1)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____1877 = (

let uu____1878 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____1878)))
in (match (uu____1877) with
| true -> begin
(

let uu____1879 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____1879))
end
| uu____1888 -> begin
()
end));
(

let uu____1889 = (force_sort' e1)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) uu____1889));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = uu____1902; FStar_Syntax_Syntax.pos = uu____1903; FStar_Syntax_Syntax.vars = uu____1904}, args)) -> begin
((

let uu____1931 = (

let uu____1932 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____1932 Prims.op_Negation))
in (match (uu____1931) with
| true -> begin
(

let uu____1933 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____1933))
end
| uu____1942 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(

let uu____2021 = (force_sort' e1)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))) uu____2021))
end
| ((arg)::args2, ((argpat, uu____2034))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____2084)) -> begin
(

let x = (

let uu____2100 = (force_sort e2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) uu____2100))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____2114) -> begin
(

let pat = (

let uu____2129 = (aux argpat e2)
in (

let uu____2130 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____2129), (uu____2130))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____2133 -> begin
(

let uu____2147 = (

let uu____2148 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____2149 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____2148 uu____2149)))
in (failwith uu____2147))
end))
in (match_args [] args argpats)));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = uu____2159; FStar_Syntax_Syntax.pos = uu____2160; FStar_Syntax_Syntax.vars = uu____2161}, uu____2162); FStar_Syntax_Syntax.tk = uu____2163; FStar_Syntax_Syntax.pos = uu____2164; FStar_Syntax_Syntax.vars = uu____2165}, args)) -> begin
((

let uu____2196 = (

let uu____2197 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____2197 Prims.op_Negation))
in (match (uu____2196) with
| true -> begin
(

let uu____2198 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2198))
end
| uu____2207 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(

let uu____2286 = (force_sort' e1)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))) uu____2286))
end
| ((arg)::args2, ((argpat, uu____2299))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____2349)) -> begin
(

let x = (

let uu____2365 = (force_sort e2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) uu____2365))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____2379) -> begin
(

let pat = (

let uu____2394 = (aux argpat e2)
in (

let uu____2395 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____2394), (uu____2395))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____2398 -> begin
(

let uu____2412 = (

let uu____2413 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____2414 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____2413 uu____2414)))
in (failwith uu____2412))
end))
in (match_args [] args argpats)));
)
end
| uu____2421 -> begin
(

let uu____2424 = (

let uu____2425 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____2426 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____2427 = (FStar_Syntax_Print.term_to_string exp)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____2425 uu____2426 uu____2427))))
in (failwith uu____2424))
end))))
in (aux p exp))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = FStar_Pervasives_Native.Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk1 = (fun f -> ((FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____2461 -> (match (uu____2461) with
| (p, i) -> begin
(

let uu____2471 = (decorated_pattern_as_term p)
in (match (uu____2471) with
| (vars, te) -> begin
(

let uu____2484 = (

let uu____2487 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____2487)))
in ((vars), (uu____2484)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____2495 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____2495)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____2498 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____2498)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____2501 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____2501)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2515 = (

let uu____2523 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____2523 FStar_List.unzip))
in (match (uu____2515) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____2581 = (

let uu____2582 = (

let uu____2583 = (

let uu____2593 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____2593), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____2583))
in (mk1 uu____2582))
in ((vars1), (uu____2581))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____2622))::[] -> begin
wp
end
| uu____2635 -> begin
(

let uu____2641 = (

let uu____2642 = (

let uu____2643 = (FStar_List.map (fun uu____2647 -> (match (uu____2647) with
| (x, uu____2651) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____2643 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____2642))
in (failwith uu____2641))
end)
in (

let uu____2655 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____2655), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____2669 = (destruct_comp c)
in (match (uu____2669) with
| (u, uu____2674, wp) -> begin
(

let uu____2676 = (

let uu____2682 = (

let uu____2683 = (lift.FStar_TypeChecker_Env.mlift_wp c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____2683))
in (uu____2682)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____2676; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____2693 = (

let uu____2697 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____2698 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____2697 uu____2698)))
in (match (uu____2693) with
| (m, uu____2700, uu____2701) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____2711 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____2711) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____2712 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____2736 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____2736) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____2758 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____2758) with
| (a, kwp) -> begin
(

let uu____2775 = (destruct_comp m1)
in (

let uu____2779 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____2775), (uu____2779))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (

let uu____2827 = (

let uu____2828 = (

let uu____2834 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2834)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____2828; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp uu____2827)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (match ((FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____2863 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu___128_2870 = lc
in (

let uu____2871 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___128_2870.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____2871; FStar_Syntax_Syntax.cflags = uu___128_2870.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2874 -> (

let uu____2875 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst1 uu____2875)))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2879 = (

let uu____2880 = (FStar_Syntax_Subst.compress t)
in uu____2880.FStar_Syntax_Syntax.n)
in (match (uu____2879) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2883) -> begin
true
end
| uu____2891 -> begin
false
end)))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____2903 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____2903) with
| true -> begin
c
end
| uu____2904 -> begin
(

let uu____2905 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2905) with
| true -> begin
c
end
| uu____2906 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____2935 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2935)::[])
in (

let us = (

let uu____2938 = (

let uu____2940 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____2940)::[])
in (u_res)::uu____2938)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some (FStar_Util.Inr (((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let uu____2951 = (

let uu____2952 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____2953 = (

let uu____2954 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____2955 = (

let uu____2957 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____2958 = (

let uu____2960 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____2960)::[])
in (uu____2957)::uu____2958))
in (uu____2954)::uu____2955))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2952 uu____2953)))
in (uu____2951 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____2966 = (destruct_comp c1)
in (match (uu____2966) with
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

let close1 = (fun uu____2989 -> (

let uu____2990 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp env bvs uu____2990)))
in (

let uu___129_2991 = lc
in {FStar_Syntax_Syntax.eff_name = uu___129_2991.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___129_2991.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___129_2991.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close1})))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v1 -> (

let c = (

let uu____3002 = (

let uu____3003 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____3003))
in (match (uu____3002) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____3004 -> begin
(

let m = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (

let uu____3008 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3008) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____3009 -> begin
(

let uu____3010 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____3010) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____3016 = (

let uu____3017 = (

let uu____3018 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____3019 = (

let uu____3020 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____3021 = (

let uu____3023 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____3023)::[])
in (uu____3020)::uu____3021))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3018 uu____3019)))
in (uu____3017 (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env uu____3016)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
in ((

let uu____3029 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____3029) with
| true -> begin
(

let uu____3030 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____3031 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____3032 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____3030 uu____3031 uu____3032))))
end
| uu____3033 -> begin
()
end));
c;
)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____3049 -> (match (uu____3049) with
| (b, lc2) -> begin
(

let lc11 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc21 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc11 lc21)
in ((

let uu____3059 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____3059) with
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

let uu____3062 = (match (e1opt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (

let uu____3064 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____3065 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" uu____3062 uu____3064 bstr uu____3065)))))
end
| uu____3066 -> begin
()
end));
(

let bind_it = (fun uu____3070 -> (

let uu____3071 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3071) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____3073 -> begin
(

let c1 = (lc11.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc21.FStar_Syntax_Syntax.comp ())
in ((

let uu____3081 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____3081) with
| true -> begin
(

let uu____3082 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____3084 = (FStar_Syntax_Print.lcomp_to_string lc11)
in (

let uu____3085 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____3086 = (FStar_Syntax_Print.lcomp_to_string lc21)
in (

let uu____3087 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" uu____3082 uu____3084 uu____3085 uu____3086 uu____3087))))))
end
| uu____3088 -> begin
()
end));
(

let try_simplify = (fun uu____3098 -> (

let aux = (fun uu____3108 -> (

let uu____3109 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____3109) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____3128) -> begin
(

let uu____3129 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____3129) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____3142 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____3147 -> begin
(

let uu____3148 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____3148) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____3161 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____3184 = (

let uu____3187 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____3187), (reason)))
in FStar_Util.Inl (uu____3184))
end
| uu____3190 -> begin
(aux ())
end))
in (

let rec maybe_close = (fun t x c -> (

let uu____3205 = (

let uu____3206 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in uu____3206.FStar_Syntax_Syntax.n)
in (match (uu____3205) with
| FStar_Syntax_Syntax.Tm_refine (y, uu____3210) -> begin
(maybe_close y.FStar_Syntax_Syntax.sort x c)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____3216 -> begin
c
end)))
in (

let uu____3217 = (

let uu____3218 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____3218))
in (match (uu____3217) with
| true -> begin
(

let uu____3226 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3226) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____3239 -> begin
(

let uu____3240 = (

let uu____3241 = (

let uu____3244 = (FStar_TypeChecker_Env.get_range env)
in (("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad"), (uu____3244)))
in FStar_Errors.Error (uu____3241))
in (FStar_Pervasives.raise uu____3240))
end))
end
| uu____3251 -> begin
(

let uu____3252 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____3252) with
| true -> begin
(subst_c2 "both total")
end
| uu____3259 -> begin
(

let uu____3260 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3260) with
| true -> begin
(

let uu____3267 = (

let uu____3270 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____3270), ("both gtot")))
in FStar_Util.Inl (uu____3267))
end
| uu____3273 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____3286 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____3287 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____3287))))
in (match (uu____3286) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___130_3296 = x
in {FStar_Syntax_Syntax.ppname = uu___130_3296.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___130_3296.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____3297 = (

let uu____3300 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____3300), ("c1 Tot")))
in FStar_Util.Inl (uu____3297))))
end
| uu____3303 -> begin
(aux ())
end))
end
| uu____3304 -> begin
(aux ())
end)
end))
end))
end))))))
in (

let uu____3309 = (try_simplify ())
in (match (uu____3309) with
| FStar_Util.Inl (c, reason) -> begin
((

let uu____3327 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____3327) with
| true -> begin
(

let uu____3328 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____3329 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____3330 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print4 "Simplified (because %s) bind %s %s to %s\n" reason uu____3328 uu____3329 uu____3330))))
end
| uu____3331 -> begin
()
end));
c;
)
end
| FStar_Util.Inr (reason) -> begin
(

let uu____3337 = (lift_and_destruct env c1 c2)
in (match (uu____3337) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3371 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____3371)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____3373 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3373)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some (FStar_Util.Inr (((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____3396 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____3397 = (

let uu____3399 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3400 = (

let uu____3402 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____3403 = (

let uu____3405 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____3406 = (

let uu____3408 = (

let uu____3409 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____3409))
in (uu____3408)::[])
in (uu____3405)::uu____3406))
in (uu____3402)::uu____3403))
in (uu____3399)::uu____3400))
in (uu____3396)::uu____3397))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (

let uu____3414 = (

let uu____3415 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3415 wp_args))
in (uu____3414 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
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

let uu____3459 = (

let uu____3460 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____3460))
in (match (uu____3459) with
| true -> begin
f
end
| uu____3461 -> begin
(

let uu____3462 = (reason1 ())
in (label uu____3462 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___131_3473 = g
in (

let uu____3474 = (

let uu____3475 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____3475))
in {FStar_TypeChecker_Env.guard_f = uu____3474; FStar_TypeChecker_Env.deferred = uu___131_3473.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___131_3473.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___131_3473.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____3485 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____3502 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3506 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3506) with
| true -> begin
c
end
| uu____3509 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____3513 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3513) with
| true -> begin
c
end
| uu____3516 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____3518 = (destruct_comp c1)
in (match (uu____3518) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____3531 = (

let uu____3532 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____3533 = (

let uu____3534 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3535 = (

let uu____3537 = (FStar_Syntax_Syntax.as_arg f1)
in (

let uu____3538 = (

let uu____3540 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3540)::[])
in (uu____3537)::uu____3538))
in (uu____3534)::uu____3535))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3532 uu____3533)))
in (uu____3531 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 c1.FStar_Syntax_Syntax.flags)))
end)))
end))
end)
end))))
in (

let uu___132_3545 = lc
in {FStar_Syntax_Syntax.eff_name = uu___132_3545.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___132_3545.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___132_3545.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> (

let uu____3572 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____3572) with
| true -> begin
((lc), (g0))
end
| uu____3575 -> begin
((

let uu____3577 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3577) with
| true -> begin
(

let uu____3578 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____3579 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" uu____3578 uu____3579)))
end
| uu____3580 -> begin
()
end));
(

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___98_3585 -> (match (uu___98_3585) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| uu____3587 -> begin
[]
end))))
in (

let strengthen = (fun uu____3593 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____3599 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____3601 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____3601) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c1 = (

let uu____3608 = ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (

let uu____3609 = (FStar_Syntax_Util.is_partial_return c)
in (not (uu____3609))))
in (match (uu____3608) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" FStar_Pervasives_Native.None (FStar_Syntax_Util.comp_result c))
in (

let xret = (

let uu____3616 = (

let uu____3617 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort uu____3617))
in (FStar_Syntax_Util.comp_set_flags uu____3616 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc1 = (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc1.FStar_Syntax_Syntax.comp ()))))
end
| uu____3620 -> begin
c
end))
in ((

let uu____3622 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3622) with
| true -> begin
(

let uu____3623 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____3624 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____3623 uu____3624)))
end
| uu____3625 -> begin
()
end));
(

let c2 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____3627 = (destruct_comp c2)
in (match (uu____3627) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____3640 = (

let uu____3641 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____3642 = (

let uu____3643 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3644 = (

let uu____3646 = (

let uu____3647 = (

let uu____3648 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____3648 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3647))
in (

let uu____3649 = (

let uu____3651 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3651)::[])
in (uu____3646)::uu____3649))
in (uu____3643)::uu____3644))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3641 uu____3642)))
in (uu____3640 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in ((

let uu____3657 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3657) with
| true -> begin
(

let uu____3658 = (FStar_Syntax_Print.term_to_string wp1)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" uu____3658))
end
| uu____3659 -> begin
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

let uu____3661 = (

let uu___133_3662 = lc
in (

let uu____3663 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____3664 = (

let uu____3666 = ((FStar_Syntax_Util.is_pure_lcomp lc) && (

let uu____3667 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation uu____3667)))
in (match (uu____3666) with
| true -> begin
flags
end
| uu____3669 -> begin
[]
end))
in {FStar_Syntax_Syntax.eff_name = uu____3663; FStar_Syntax_Syntax.res_typ = uu___133_3662.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu____3664; FStar_Syntax_Syntax.comp = strengthen})))
in ((uu____3661), ((

let uu___134_3670 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___134_3670.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___134_3670.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___134_3670.FStar_TypeChecker_Env.implicits}))))));
)
end)))


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____3685 = (

let uu____3688 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____3689 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____3688), (uu____3689))))
in (match (uu____3685) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (

let uu____3698 = (

let uu____3699 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (

let uu____3700 = (

let uu____3701 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3702 = (

let uu____3704 = (FStar_Syntax_Syntax.as_arg yexp)
in (uu____3704)::[])
in (uu____3701)::uu____3702))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3699 uu____3700)))
in (uu____3698 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let x_eq_y_yret = (

let uu____3712 = (

let uu____3713 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (

let uu____3714 = (

let uu____3715 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3716 = (

let uu____3718 = (

let uu____3719 = (FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3719))
in (

let uu____3720 = (

let uu____3722 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (uu____3722)::[])
in (uu____3718)::uu____3720))
in (uu____3715)::uu____3716))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3713 uu____3714)))
in (uu____3712 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (

let uu____3730 = (

let uu____3731 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (

let uu____3732 = (

let uu____3733 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3734 = (

let uu____3736 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3737 = (

let uu____3739 = (

let uu____3740 = (

let uu____3741 = (

let uu____3742 = (FStar_Syntax_Syntax.mk_binder y)
in (uu____3742)::[])
in (FStar_Syntax_Util.abs uu____3741 x_eq_y_yret (FStar_Pervasives_Native.Some (FStar_Util.Inr (((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3740))
in (uu____3739)::[])
in (uu____3736)::uu____3737))
in (uu____3733)::uu____3734))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3731 uu____3732)))
in (uu____3730 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (

let uu____3758 = (FStar_TypeChecker_Env.get_range env)
in (bind uu____3758 env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp comp) ((FStar_Pervasives_Native.Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun uu____3776 -> (

let uu____3777 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3777) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end
| uu____3779 -> begin
(

let uu____3780 = (

let uu____3793 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (

let uu____3794 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____3793 uu____3794)))
in (match (uu____3780) with
| ((md, uu____3796, uu____3797), (u_res_t, res_t, wp_then), (uu____3801, uu____3802, wp_else)) -> begin
(

let ifthenelse = (fun md1 res_t1 g wp_t wp_e -> (

let uu____3831 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____3832 = (

let uu____3833 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md1 md1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3834 = (

let uu____3835 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____3836 = (

let uu____3838 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____3839 = (

let uu____3841 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____3842 = (

let uu____3844 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____3844)::[])
in (uu____3841)::uu____3842))
in (uu____3838)::uu____3839))
in (uu____3835)::uu____3836))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3833 uu____3834)))
in (uu____3832 FStar_Pervasives_Native.None uu____3831))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let uu____3852 = (

let uu____3853 = (FStar_Options.split_cases ())
in (uu____3853 > (Prims.parse_int "0")))
in (match (uu____3852) with
| true -> begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end
| uu____3855 -> begin
(

let wp1 = (

let uu____3859 = (

let uu____3860 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____3861 = (

let uu____3862 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3863 = (

let uu____3865 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3865)::[])
in (uu____3862)::uu____3863))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3860 uu____3861)))
in (uu____3859 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end))
end)))
in (

let uu____3870 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____3870; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____3877 = (

let uu____3878 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____3878))
in (FStar_Syntax_Syntax.fvar uu____3877 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____3898 -> (match (uu____3898) with
| (uu____3901, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun uu____3906 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____3908 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3908) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____3909 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____3928 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____3929 = (

let uu____3930 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3931 = (

let uu____3932 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____3933 = (

let uu____3935 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____3936 = (

let uu____3938 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____3939 = (

let uu____3941 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____3941)::[])
in (uu____3938)::uu____3939))
in (uu____3935)::uu____3936))
in (uu____3932)::uu____3933))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3930 uu____3931)))
in (uu____3929 FStar_Pervasives_Native.None uu____3928))))
in (

let default_case = (

let post_k = (

let uu____3950 = (

let uu____3954 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____3954)::[])
in (

let uu____3955 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3950 uu____3955)))
in (

let kwp = (

let uu____3961 = (

let uu____3965 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____3965)::[])
in (

let uu____3966 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3961 uu____3966)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____3971 = (

let uu____3972 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____3972)::[])
in (

let uu____3973 = (

let uu____3974 = (

let uu____3977 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____3977))
in (

let uu____3978 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____3974 uu____3978)))
in (FStar_Syntax_Util.abs uu____3971 uu____3973 (FStar_Pervasives_Native.Some (FStar_Util.Inr (((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun uu____3992 celse -> (match (uu____3992) with
| (g, cthen) -> begin
(

let uu____3998 = (

let uu____4011 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____4011 celse))
in (match (uu____3998) with
| ((md, uu____4013, uu____4014), (uu____4015, uu____4016, wp_then), (uu____4018, uu____4019, wp_else)) -> begin
(

let uu____4030 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____4030 []))
end))
end)) lcases default_case)
in (

let uu____4031 = (

let uu____4032 = (FStar_Options.split_cases ())
in (uu____4032 > (Prims.parse_int "0")))
in (match (uu____4031) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| uu____4033 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____4036 = (destruct_comp comp1)
in (match (uu____4036) with
| (uu____4040, uu____4041, wp) -> begin
(

let wp1 = (

let uu____4046 = (

let uu____4047 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____4048 = (

let uu____4049 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4050 = (

let uu____4052 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4052)::[])
in (uu____4049)::uu____4050))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4047 uu____4048)))
in (uu____4046 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 []))
end))))
end)))))
end))))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let flags = (

let uu____4068 = (((

let uu____4069 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____4069))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (

let uu____4070 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____4070))))
in (match (uu____4068) with
| true -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____4072 -> begin
lc.FStar_Syntax_Syntax.cflags
end))
in (

let refine1 = (fun uu____4078 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____4082 = ((

let uu____4083 = (is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name)
in (not (uu____4083))) || env.FStar_TypeChecker_Env.lax)
in (match (uu____4082) with
| true -> begin
c
end
| uu____4086 -> begin
(

let uu____4087 = (FStar_Syntax_Util.is_partial_return c)
in (match (uu____4087) with
| true -> begin
c
end
| uu____4090 -> begin
(

let uu____4091 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____4091) with
| true -> begin
(

let uu____4094 = (

let uu____4095 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (not (uu____4095)))
in (match (uu____4094) with
| true -> begin
(

let uu____4098 = (

let uu____4099 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____4100 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" uu____4099 uu____4100)))
in (failwith uu____4098))
end
| uu____4103 -> begin
(

let retc = (return_value env (FStar_Syntax_Util.comp_result c) e)
in (

let uu____4105 = (

let uu____4106 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____4106)))
in (match (uu____4105) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___135_4111 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___135_4111.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___135_4111.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___135_4111.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____4112 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags)
end)))
end))
end
| uu____4113 -> begin
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

let uu____4122 = (

let uu____4125 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____4125 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4122))
in (

let eq1 = (

let uu____4129 = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Util.mk_eq2 uu____4129 t xexp e))
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____4131 = (

let uu____4132 = (

let uu____4137 = (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None (FStar_Syntax_Util.lcomp_of_comp c2) ((FStar_Pervasives_Native.Some (x)), (eq_ret)))
in uu____4137.FStar_Syntax_Syntax.comp)
in (uu____4132 ()))
in (FStar_Syntax_Util.comp_set_flags uu____4131 flags))))))))))
end))
end))
end))))
in (

let uu___136_4139 = lc
in {FStar_Syntax_Syntax.eff_name = uu___136_4139.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___136_4139.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine1}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____4158 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____4158) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4163 = (

let uu____4164 = (

let uu____4167 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____4168 = (FStar_TypeChecker_Env.get_range env)
in ((uu____4167), (uu____4168))))
in FStar_Errors.Error (uu____4164))
in (FStar_Pervasives.raise uu____4163))
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____4194 = (

let uu____4195 = (FStar_Syntax_Subst.compress t2)
in uu____4195.FStar_Syntax_Syntax.n)
in (match (uu____4194) with
| FStar_Syntax_Syntax.Tm_type (uu____4198) -> begin
true
end
| uu____4199 -> begin
false
end))))
in (

let uu____4200 = (

let uu____4201 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in uu____4201.FStar_Syntax_Syntax.n)
in (match (uu____4200) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____4207 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let lc1 = (

let uu____4214 = (

let uu____4215 = (

let uu____4216 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4216))
in ((FStar_Pervasives_Native.None), (uu____4215)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____4214))
in (

let e1 = (

let uu____4225 = (

let uu____4226 = (

let uu____4227 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4227)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4226))
in (uu____4225 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____4234 -> begin
((e), (lc))
end))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____4254 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____4254) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____4267 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____4279 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4279), (false)))
end
| uu____4282 -> begin
(

let uu____4283 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4283), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____4289) -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___137_4292 = lc
in {FStar_Syntax_Syntax.eff_name = uu___137_4292.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___137_4292.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___137_4292.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard));
)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____4296 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____4296) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___138_4301 = lc
in {FStar_Syntax_Syntax.eff_name = uu___138_4301.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___138_4301.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___138_4301.FStar_Syntax_Syntax.comp})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___139_4304 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___139_4304.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___139_4304.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___139_4304.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____4310 -> (

let uu____4311 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4311) with
| true -> begin
(lc.FStar_Syntax_Syntax.comp ())
end
| uu____4314 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let uu____4316 = (

let uu____4317 = (FStar_Syntax_Subst.compress f1)
in uu____4317.FStar_Syntax_Syntax.n)
in (match (uu____4316) with
| FStar_Syntax_Syntax.Tm_abs (uu____4322, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4324; FStar_Syntax_Syntax.pos = uu____4325; FStar_Syntax_Syntax.vars = uu____4326}, uu____4327) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___140_4351 = lc
in {FStar_Syntax_Syntax.eff_name = uu___140_4351.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___140_4351.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___140_4351.FStar_Syntax_Syntax.comp})
in (lc1.FStar_Syntax_Syntax.comp ()))
end
| uu____4352 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in ((

let uu____4357 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4357) with
| true -> begin
(

let uu____4358 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____4359 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____4360 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____4361 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____4358 uu____4359 uu____4360 uu____4361)))))
end
| uu____4362 -> begin
()
end));
(

let ct = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4364 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____4364) with
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

let uu____4375 = (destruct_comp ct)
in (match (uu____4375) with
| (u_t, uu____4382, uu____4383) -> begin
(

let wp = (

let uu____4387 = (

let uu____4388 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (

let uu____4389 = (

let uu____4390 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____4391 = (

let uu____4393 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____4393)::[])
in (uu____4390)::uu____4391))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4388 uu____4389)))
in (uu____4387 (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos))
in (

let cret = (

let uu____4399 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4399))
in (

let guard = (match (apply_guard1) with
| true -> begin
(

let uu____4409 = (

let uu____4410 = (

let uu____4411 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____4411)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____4410))
in (uu____4409 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f1.FStar_Syntax_Syntax.pos))
end
| uu____4416 -> begin
f1
end)
in (

let uu____4417 = (

let uu____4420 = (FStar_All.pipe_left (fun _0_29 -> FStar_Pervasives_Native.Some (_0_29)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____4431 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____4432 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____4420 uu____4431 e cret uu____4432))))
in (match (uu____4417) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___141_4438 = x
in {FStar_Syntax_Syntax.ppname = uu___141_4438.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___141_4438.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____4440 = (

let uu____4441 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4441))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____4440 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (c1.FStar_Syntax_Syntax.comp ())
in ((

let uu____4451 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4451) with
| true -> begin
(

let uu____4452 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____4452))
end
| uu____4453 -> begin
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

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___99_4458 -> (match (uu___99_4458) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____4460 -> begin
[]
end))))
in (

let lc1 = (

let uu___142_4462 = lc
in (

let uu____4463 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____4463; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g2 = (

let uu___143_4465 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___143_4465.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___143_4465.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___143_4465.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____4485 = (

let uu____4486 = (

let uu____4487 = (

let uu____4488 = (

let uu____4489 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____4489))
in (uu____4488)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____4487))
in (uu____4486 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____4485))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____4498 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____4498) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____4505 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____4509) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____4518) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____4535))::((ens, uu____4537))::uu____4538 -> begin
(

let uu____4560 = (

let uu____4562 = (norm req)
in FStar_Pervasives_Native.Some (uu____4562))
in (

let uu____4563 = (

let uu____4564 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm uu____4564))
in ((uu____4560), (uu____4563))))
end
| uu____4566 -> begin
(

let uu____4572 = (

let uu____4573 = (

let uu____4576 = (

let uu____4577 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____4577))
in ((uu____4576), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____4573))
in (FStar_Pervasives.raise uu____4572))
end)
end
| uu____4581 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____4587))::uu____4588 -> begin
(

let uu____4602 = (

let uu____4605 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4605))
in (match (uu____4602) with
| (us_r, uu____4622) -> begin
(

let uu____4623 = (

let uu____4626 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4626))
in (match (uu____4623) with
| (us_e, uu____4643) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____4646 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4646 us_r))
in (

let as_ens = (

let uu____4648 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4648 us_e))
in (

let req = (

let uu____4652 = (

let uu____4653 = (

let uu____4654 = (

let uu____4661 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4661)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____4654)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____4653))
in (uu____4652 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____4677 = (

let uu____4678 = (

let uu____4679 = (

let uu____4686 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4686)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____4679)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____4678))
in (uu____4677 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____4699 = (

let uu____4701 = (norm req)
in FStar_Pervasives_Native.Some (uu____4701))
in (

let uu____4702 = (

let uu____4703 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm uu____4703))
in ((uu____4699), (uu____4702)))))))))
end))
end))
end
| uu____4705 -> begin
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

let uu____4725 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____4725) with
| true -> begin
(

let uu____4726 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____4727 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____4726 uu____4727)))
end
| uu____4728 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____4748 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____4748) with
| true -> begin
(

let uu____4749 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____4750 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____4749 uu____4750)))
end
| uu____4751 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____4755 = (

let uu____4756 = (

let uu____4757 = (FStar_Syntax_Subst.compress t)
in uu____4757.FStar_Syntax_Syntax.n)
in (match (uu____4756) with
| FStar_Syntax_Syntax.Tm_app (uu____4760) -> begin
false
end
| uu____4770 -> begin
true
end))
in (match (uu____4755) with
| true -> begin
t
end
| uu____4771 -> begin
(

let uu____4772 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4772) with
| (head1, args) -> begin
(

let uu____4798 = (

let uu____4799 = (

let uu____4800 = (FStar_Syntax_Subst.compress head1)
in uu____4800.FStar_Syntax_Syntax.n)
in (match (uu____4799) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____4803 -> begin
false
end))
in (match (uu____4798) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____4819 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____4825 -> begin
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
| uu____4842 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____4847 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____4847) with
| (formals, uu____4856) -> begin
(

let n_implicits = (

let uu____4868 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____4905 -> (match (uu____4905) with
| (uu____4909, imp) -> begin
((imp = FStar_Pervasives_Native.None) || (imp = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)))
end))))
in (match (uu____4868) with
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

let uu____4981 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____4981) with
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

let uu____4995 = (

let uu____4996 = (

let uu____4999 = (

let uu____5000 = (FStar_Util.string_of_int n_expected)
in (

let uu____5004 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5005 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____5000 uu____5004 uu____5005))))
in (

let uu____5009 = (FStar_TypeChecker_Env.get_range env)
in ((uu____4999), (uu____5009))))
in FStar_Errors.Error (uu____4996))
in (FStar_Pervasives.raise uu____4995))
end
| uu____5011 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___100_5022 -> (match (uu___100_5022) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____5041 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____5041) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_30), uu____5102) when (_0_30 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____5124, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____5143 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____5143) with
| (v1, uu____5164, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____5174 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____5174) with
| (args, bs3, subst3, g') -> begin
(

let uu____5223 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____5223)))
end)))
end)))
end
| (uu____5237, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____5261 = (

let uu____5275 = (inst_n_binders t)
in (aux [] uu____5275 bs1))
in (match (uu____5261) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____5313) -> begin
((e), (torig), (guard))
end
| (uu____5329, []) when (

let uu____5345 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____5345))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____5346 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____5365 -> begin
(FStar_Syntax_Util.arrow bs2 c1)
end)
in (

let t2 = (FStar_Syntax_Subst.subst subst1 t1)
in (

let e1 = ((FStar_Syntax_Syntax.mk_Tm_app e args) (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((e1), (t2), (guard)))))
end)
end)))
end))
end
| uu____5380 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs = (fun univs1 -> (

let uu____5392 = (

let uu____5394 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____5394 (FStar_List.map (fun u -> (

let uu____5404 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____5404 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____5392 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____5416 = (FStar_Util.set_is_empty x)
in (match (uu____5416) with
| true -> begin
[]
end
| uu____5418 -> begin
(

let s = (

let uu____5421 = (

let uu____5423 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____5423))
in (FStar_All.pipe_right uu____5421 FStar_Util.set_elements))
in ((

let uu____5428 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5428) with
| true -> begin
(

let uu____5429 = (

let uu____5430 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____5430))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____5429))
end
| uu____5435 -> begin
()
end));
(

let r = (

let uu____5438 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____5438))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____5450 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5450) with
| true -> begin
(

let uu____5451 = (

let uu____5452 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____5452))
in (

let uu____5454 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____5455 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____5451 uu____5454 uu____5455))))
end
| uu____5456 -> begin
()
end));
(FStar_Unionfind.change u (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_name (u_name))));
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

let uu____5473 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____5473 FStar_Util.fifo_set_elements))
in univnames1))))


let maybe_set_tk = (fun ts uu___101_5500 -> (match (uu___101_5500) with
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
| ([], uu____5541) -> begin
generalized_univ_names
end
| (uu____5545, []) -> begin
explicit_univ_names
end
| uu____5549 -> begin
(

let uu____5554 = (

let uu____5555 = (

let uu____5558 = (

let uu____5559 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____5559))
in ((uu____5558), (t.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____5555))
in (FStar_Pervasives.raise uu____5554))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in (

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____5573 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5573) with
| true -> begin
(

let uu____5574 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____5574))
end
| uu____5576 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____5580 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5580) with
| true -> begin
(

let uu____5581 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" uu____5581))
end
| uu____5582 -> begin
()
end));
(

let univs2 = (check_universe_generalization univnames1 gen1 t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs2 t)
in (

let uu____5586 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs2), (ts)) uu____5586))));
));
)))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list FStar_Pervasives_Native.option = (fun env ecs -> (

let uu____5616 = (

let uu____5617 = (FStar_Util.for_all (fun uu____5622 -> (match (uu____5622) with
| (uu____5627, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation uu____5617))
in (match (uu____5616) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5644 -> begin
(

let norm = (fun c -> ((

let uu____5650 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5650) with
| true -> begin
(

let uu____5651 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____5651))
end
| uu____5652 -> begin
()
end));
(

let c1 = (

let uu____5654 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____5654) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
| uu____5655 -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end))
in ((

let uu____5657 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5657) with
| true -> begin
(

let uu____5658 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5658))
end
| uu____5659 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____5692 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____5692 FStar_Util.set_elements)))
in (

let uu____5736 = (

let uu____5754 = (FStar_All.pipe_right ecs (FStar_List.map (fun uu____5809 -> (match (uu____5809) with
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
in (FStar_All.pipe_right uu____5754 FStar_List.unzip))
in (match (uu____5736) with
| (univs1, uvars1) -> begin
(

let univs2 = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs1)
in (

let gen_univs1 = (gen_univs env univs2)
in ((

let uu____5971 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5971) with
| true -> begin
(FStar_All.pipe_right gen_univs1 (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end
| uu____5974 -> begin
()
end));
(

let ecs1 = (FStar_All.pipe_right uvars1 (FStar_List.map (fun uu____6013 -> (match (uu____6013) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____6070 -> (match (uu____6070) with
| (u, k) -> begin
(

let uu____6090 = (FStar_Unionfind.find u)
in (match (uu____6090) with
| FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = uu____6101; FStar_Syntax_Syntax.pos = uu____6102; FStar_Syntax_Syntax.vars = uu____6103}) -> begin
((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (uu____6109, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = uu____6111; FStar_Syntax_Syntax.pos = uu____6112; FStar_Syntax_Syntax.vars = uu____6113}, uu____6114); FStar_Syntax_Syntax.tk = uu____6115; FStar_Syntax_Syntax.pos = uu____6116; FStar_Syntax_Syntax.vars = uu____6117}) -> begin
((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (uu____6145) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____6153 -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env k)
in (

let uu____6158 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____6158) with
| (bs, kres) -> begin
(

let a = (

let uu____6182 = (

let uu____6184 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_31 -> FStar_Pervasives_Native.Some (_0_31)) uu____6184))
in (FStar_Syntax_Syntax.new_bv uu____6182 kres))
in (

let t = (

let uu____6187 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____6188 = (

let uu____6195 = (

let uu____6201 = (

let uu____6202 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp uu____6202))
in FStar_Util.Inl (uu____6201))
in FStar_Pervasives_Native.Some (uu____6195))
in (FStar_Syntax_Util.abs bs uu____6187 uu____6188)))
in ((FStar_Syntax_Util.set_uvar u t);
((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)));
)))
end)))
end))
end))))
in (

let uu____6217 = (match (((tvars), (gen_univs1))) with
| ([], []) -> begin
(

let uu____6235 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in ((uu____6235), (c)))
end
| ([], uu____6236) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in ((e1), (c1))))
end
| uu____6248 -> begin
(

let uu____6256 = ((e), (c))
in (match (uu____6256) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let t = (

let uu____6268 = (

let uu____6269 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____6269.FStar_Syntax_Syntax.n)
in (match (uu____6268) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____6286 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____6286) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs1) cod1)
end))
end
| uu____6296 -> begin
(FStar_Syntax_Util.arrow tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs tvars e1 (FStar_Pervasives_Native.Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c1)))))
in (

let uu____6306 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____6306)))))))
end))
end)
in (match (uu____6217) with
| (e1, c1) -> begin
((gen_univs1), (e1), (c1))
end)))
end))))
in FStar_Pervasives_Native.Some (ecs1));
)))
end)))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> ((

let uu____6344 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6344) with
| true -> begin
(

let uu____6345 = (

let uu____6346 = (FStar_List.map (fun uu____6351 -> (match (uu____6351) with
| (lb, uu____6356, uu____6357) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____6346 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____6345))
end
| uu____6359 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____6367 -> (match (uu____6367) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____6382 = (

let uu____6389 = (FStar_All.pipe_right lecs (FStar_List.map (fun uu____6405 -> (match (uu____6405) with
| (uu____6411, e, c) -> begin
((e), (c))
end))))
in (gen env uu____6389))
in (match (uu____6382) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____6443 -> (match (uu____6443) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| FStar_Pervasives_Native.Some (ecs) -> begin
(FStar_List.map2 (fun uu____6487 uu____6488 -> (match (((uu____6487), (uu____6488))) with
| ((l, uu____6521, uu____6522), (us, e, c)) -> begin
((

let uu____6548 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____6548) with
| true -> begin
(

let uu____6549 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____6550 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____6551 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____6552 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" uu____6549 uu____6550 uu____6551 uu____6552)))))
end
| uu____6553 -> begin
()
end));
((l), (us), (e), (c));
)
end)) lecs ecs)
end))
in (FStar_List.map2 (fun univnames1 uu____6571 -> (match (uu____6571) with
| (l, generalized_univs, t, c) -> begin
(

let uu____6589 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____6589), (t), (c)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____6621 -> begin
(

let uu____6622 = (FStar_TypeChecker_Rel.try_subtype env2 t11 t21)
in (match (uu____6622) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____6626 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_32 -> FStar_Pervasives_Native.Some (_0_32)) uu____6626))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____6632 = (

let uu____6633 = (FStar_Syntax_Subst.compress e1)
in uu____6633.FStar_Syntax_Syntax.n)
in (match (uu____6632) with
| FStar_Syntax_Syntax.Tm_name (uu____6636) -> begin
true
end
| uu____6637 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___144_6655 = x
in {FStar_Syntax_Syntax.ppname = uu___144_6655.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___144_6655.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) e2.FStar_Syntax_Syntax.pos)
end
| uu____6656 -> begin
(

let uu___145_6657 = e2
in (

let uu____6658 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = uu___145_6657.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu____6658; FStar_Syntax_Syntax.pos = uu___145_6657.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___145_6657.FStar_Syntax_Syntax.vars}))
end)))
in (

let env2 = (

let uu___146_6667 = env1
in (

let uu____6668 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___146_6667.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___146_6667.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___146_6667.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___146_6667.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___146_6667.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___146_6667.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___146_6667.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___146_6667.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___146_6667.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___146_6667.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___146_6667.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___146_6667.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___146_6667.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___146_6667.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___146_6667.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____6668; FStar_TypeChecker_Env.is_iface = uu___146_6667.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___146_6667.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___146_6667.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___146_6667.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___146_6667.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___146_6667.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___146_6667.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___146_6667.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____6669 = (check env2 t1 t2)
in (match (uu____6669) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6673 = (

let uu____6674 = (

let uu____6677 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____6678 = (FStar_TypeChecker_Env.get_range env2)
in ((uu____6677), (uu____6678))))
in FStar_Errors.Error (uu____6674))
in (FStar_Pervasives.raise uu____6673))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____6683 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____6683) with
| true -> begin
(

let uu____6684 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____6684))
end
| uu____6685 -> begin
()
end));
(

let uu____6686 = (decorate e t2)
in ((uu____6686), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____6710 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____6710) with
| true -> begin
(

let uu____6713 = (discharge g1)
in (

let uu____6714 = (lc.FStar_Syntax_Syntax.comp ())
in ((uu____6713), (uu____6714))))
end
| uu____6719 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c1 = (

let uu____6726 = (

let uu____6727 = (

let uu____6728 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____6728 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____6727 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____6726 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____6730 = (destruct_comp c1)
in (match (uu____6730) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____6742 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____6743 = (

let uu____6744 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____6745 = (

let uu____6746 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6747 = (

let uu____6749 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6749)::[])
in (uu____6746)::uu____6747))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6744 uu____6745)))
in (uu____6743 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) uu____6742)))
in ((

let uu____6755 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____6755) with
| true -> begin
(

let uu____6756 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____6756))
end
| uu____6757 -> begin
()
end));
(

let g2 = (

let uu____6759 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____6759))
in (

let uu____6760 = (discharge g2)
in (

let uu____6761 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____6760), (uu____6761)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___102_6785 -> (match (uu___102_6785) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____6791))::[] -> begin
(f fst1)
end
| uu____6804 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____6809 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____6809 (fun _0_33 -> FStar_TypeChecker_Common.NonTrivial (_0_33)))))
in (

let op_or_e = (fun e -> (

let uu____6818 = (

let uu____6821 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____6821))
in (FStar_All.pipe_right uu____6818 (fun _0_34 -> FStar_TypeChecker_Common.NonTrivial (_0_34)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_35 -> FStar_TypeChecker_Common.NonTrivial (_0_35))))
in (

let op_or_t = (fun t -> (

let uu____6832 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____6832 (fun _0_36 -> FStar_TypeChecker_Common.NonTrivial (_0_36)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_37 -> FStar_TypeChecker_Common.NonTrivial (_0_37))))
in (

let short_op_ite = (fun uu___103_6846 -> (match (uu___103_6846) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____6852))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____6867))::[] -> begin
(

let uu____6888 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____6888 (fun _0_38 -> FStar_TypeChecker_Common.NonTrivial (_0_38))))
end
| uu____6893 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____6900 = (

let uu____6905 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____6905)))
in (

let uu____6910 = (

let uu____6916 = (

let uu____6921 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____6921)))
in (

let uu____6926 = (

let uu____6932 = (

let uu____6937 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____6937)))
in (

let uu____6942 = (

let uu____6948 = (

let uu____6953 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____6953)))
in (

let uu____6958 = (

let uu____6964 = (

let uu____6969 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____6969)))
in (uu____6964)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____6948)::uu____6958))
in (uu____6932)::uu____6942))
in (uu____6916)::uu____6926))
in (uu____6900)::uu____6910))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____7010 = (FStar_Util.find_map table (fun uu____7016 -> (match (uu____7016) with
| (x, mk1) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
(

let uu____7029 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____7029))
end
| uu____7030 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (uu____7010) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____7032 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____7036 = (

let uu____7037 = (FStar_Syntax_Util.un_uinst l)
in uu____7037.FStar_Syntax_Syntax.n)
in (match (uu____7036) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____7041 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____7059))::uu____7060 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____7066 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____7070, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7071))))::uu____7072 -> begin
bs
end
| uu____7081 -> begin
(

let uu____7082 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____7082) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____7085 = (

let uu____7086 = (FStar_Syntax_Subst.compress t)
in uu____7086.FStar_Syntax_Syntax.n)
in (match (uu____7085) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____7090) -> begin
(

let uu____7101 = (FStar_Util.prefix_until (fun uu___104_7120 -> (match (uu___104_7120) with
| (uu____7124, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7125))) -> begin
false
end
| uu____7127 -> begin
true
end)) bs')
in (match (uu____7101) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____7145, uu____7146) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____7183, uu____7184) -> begin
(

let uu____7221 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____7229 -> (match (uu____7229) with
| (x, uu____7234) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____7221) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____7257 -> (match (uu____7257) with
| (x, i) -> begin
(

let uu____7268 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____7268), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____7273 -> begin
bs
end))
end))
end
| uu____7274 -> begin
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
| uu____7292 -> begin
(

let uu____7293 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) uu____7293 e.FStar_Syntax_Syntax.pos))
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____7315 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____7315) with
| true -> begin
e
end
| uu____7316 -> begin
(

let uu____7317 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) uu____7317 e.FStar_Syntax_Syntax.pos))
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____7343 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____7343) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(

let uu____7345 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) uu____7345));
)
end
| uu____7346 -> begin
()
end));
(

let fv = (

let uu____7348 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____7348 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[]), ([])))))
in (

let uu____7355 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___147_7364 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___147_7364.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___147_7364.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___147_7364.FStar_Syntax_Syntax.sigmeta})), (uu____7355)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___105_7374 -> (match (uu___105_7374) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7375 -> begin
false
end))
in (

let reducibility = (fun uu___106_7379 -> (match (uu___106_7379) with
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
| uu____7380 -> begin
false
end))
in (

let assumption = (fun uu___107_7384 -> (match (uu___107_7384) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____7385 -> begin
false
end))
in (

let reification = (fun uu___108_7389 -> (match (uu___108_7389) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____7390) -> begin
true
end
| uu____7391 -> begin
false
end))
in (

let inferred = (fun uu___109_7395 -> (match (uu___109_7395) with
| FStar_Syntax_Syntax.Discriminator (uu____7396) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____7397) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____7400) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____7405) -> begin
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
| uu____7410 -> begin
false
end))
in (

let has_eq = (fun uu___110_7414 -> (match (uu___110_7414) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____7415 -> begin
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
| FStar_Syntax_Syntax.Reflectable (uu____7449) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (x = FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7452 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____7455 = (

let uu____7456 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___111_7458 -> (match (uu___111_7458) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____7459 -> begin
false
end))))
in (FStar_All.pipe_right uu____7456 Prims.op_Negation))
in (match (uu____7455) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (

let uu____7469 = (

let uu____7470 = (

let uu____7473 = (

let uu____7474 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____7474 msg))
in ((uu____7473), (r)))
in FStar_Errors.Error (uu____7470))
in (FStar_Pervasives.raise uu____7469)))
in (

let err1 = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____7482 -> (err' ""))
in ((match (((FStar_List.length quals) <> (FStar_List.length no_dup_quals))) with
| true -> begin
(err1 "duplicate qualifiers")
end
| uu____7488 -> begin
()
end);
(

let uu____7490 = (

let uu____7491 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____7491)))
in (match (uu____7490) with
| true -> begin
(err1 "ill-formed combination")
end
| uu____7493 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7495), uu____7496, uu____7497) -> begin
((

let uu____7508 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____7508) with
| true -> begin
(err1 "recursive definitions cannot be marked inline")
end
| uu____7510 -> begin
()
end));
(

let uu____7511 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____7511) with
| true -> begin
(err1 "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____7514 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____7515) -> begin
(

let uu____7520 = (

let uu____7521 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____7521)))
in (match (uu____7520) with
| true -> begin
(err'1 ())
end
| uu____7524 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____7525) -> begin
(

let uu____7529 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____7529) with
| true -> begin
(err'1 ())
end
| uu____7531 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____7532) -> begin
(

let uu____7535 = (

let uu____7536 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption)))))
in (not (uu____7536)))
in (match (uu____7535) with
| true -> begin
(err'1 ())
end
| uu____7539 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____7540) -> begin
(

let uu____7541 = (

let uu____7542 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____7542)))
in (match (uu____7541) with
| true -> begin
(err'1 ())
end
| uu____7545 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____7546) -> begin
(

let uu____7547 = (

let uu____7548 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____7548)))
in (match (uu____7547) with
| true -> begin
(err'1 ())
end
| uu____7551 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7552) -> begin
(

let uu____7559 = (

let uu____7560 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____7560)))
in (match (uu____7559) with
| true -> begin
(err'1 ())
end
| uu____7563 -> begin
()
end))
end
| uu____7564 -> begin
()
end);
))))))
end
| uu____7565 -> begin
()
end)))))))))))


let mk_discriminator_and_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid uvs inductive_tps indices fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (FStar_Pervasives_Native.Some (p)) ptyp))
in (

let inst_univs = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) uvs)
in (

let tps = inductive_tps
in (

let arg_typ = (

let inst_tc = (

let uu____7621 = (

let uu____7624 = (

let uu____7625 = (

let uu____7630 = (

let uu____7631 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7631))
in ((uu____7630), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____7625))
in (FStar_Syntax_Syntax.mk uu____7624))
in (uu____7621 FStar_Pervasives_Native.None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7657 -> (match (uu____7657) with
| (x, imp) -> begin
(

let uu____7664 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7664), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args FStar_Pervasives_Native.None p)))
in (

let unrefined_arg_binder = (

let uu____7668 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____7668))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____7670 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____7677 = (

let uu____7678 = (

let uu____7679 = (

let uu____7680 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____7681 = (

let uu____7682 = (

let uu____7683 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7683))
in (uu____7682)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____7680 uu____7681)))
in (uu____7679 FStar_Pervasives_Native.None p))
in (FStar_Syntax_Util.b2t uu____7678))
in (FStar_Syntax_Util.refine x uu____7677)))
in (

let uu____7688 = (

let uu___148_7689 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___148_7689.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_7689.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____7688)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____7699 = (FStar_List.map (fun uu____7709 -> (match (uu____7709) with
| (x, uu____7716) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____7699 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7740 -> (match (uu____7740) with
| (x, uu____7747) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((fvq <> FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____7752 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((

let uu____7756 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____7756)) || (

let uu____7757 = (

let uu____7758 = (FStar_TypeChecker_Env.current_module env)
in uu____7758.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____7757)))
in (

let quals = (

let uu____7761 = (

let uu____7763 = (

let uu____7765 = (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit))
in (match (uu____7765) with
| true -> begin
(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____7767 -> begin
[]
end))
in (

let uu____7768 = (FStar_List.filter (fun uu___112_7770 -> (match (uu___112_7770) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7771 -> begin
false
end)) iquals)
in (FStar_List.append uu____7763 uu____7768)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::[]
end
| uu____7773 -> begin
[]
end)) uu____7761))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____7784 = (

let uu____7785 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7785))
in (FStar_Syntax_Syntax.mk_Total uu____7784))
in (

let uu____7786 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____7786)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid discriminator_name); FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta}
in ((

let uu____7789 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7789) with
| true -> begin
(

let uu____7790 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____7790))
end
| uu____7791 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____7793 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____7799 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____7822 -> (match (uu____7822) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____7838 = (

let uu____7841 = (

let uu____7842 = (

let uu____7847 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____7847), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____7842))
in (pos uu____7841))
in ((uu____7838), (b)))
end
| uu____7850 -> begin
(

let uu____7851 = (

let uu____7854 = (

let uu____7855 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7855))
in (pos uu____7854))
in ((uu____7851), (b)))
end))
end))))
in (

let pat_true = (

let uu____7869 = (

let uu____7872 = (

let uu____7873 = (

let uu____7881 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____7881), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____7873))
in (pos uu____7872))
in ((uu____7869), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_true_bool)))
in (

let pat_false = (

let uu____7907 = (

let uu____7910 = (

let uu____7911 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7911))
in (pos uu____7910))
in ((uu____7907), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst unrefined_arg_binder))
in (

let uu____7922 = (

let uu____7925 = (

let uu____7926 = (

let uu____7942 = (

let uu____7944 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____7945 = (

let uu____7947 = (FStar_Syntax_Util.branch pat_false)
in (uu____7947)::[])
in (uu____7944)::uu____7945))
in ((arg_exp), (uu____7942)))
in FStar_Syntax_Syntax.Tm_match (uu____7926))
in (FStar_Syntax_Syntax.mk uu____7925))
in (uu____7922 FStar_Pervasives_Native.None p))))))
end)
in (

let dd = (

let uu____7958 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____7958) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____7960 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____7968 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____7970 = (

let uu____7973 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____7973))
in (

let uu____7974 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____7970; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____7974}))
in (

let impl = (

let uu____7978 = (

let uu____7979 = (

let uu____7985 = (

let uu____7987 = (

let uu____7988 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____7988 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____7987)::[])
in ((((false), ((lb)::[]))), (uu____7985), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____7979))
in {FStar_Syntax_Syntax.sigel = uu____7978; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta})
in ((

let uu____8003 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8003) with
| true -> begin
(

let uu____8004 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____8004))
end
| uu____8005 -> begin
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

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____8024 -> (match (uu____8024) with
| (a, uu____8028) -> begin
(

let uu____8029 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____8029) with
| (field_name, uu____8033) -> begin
(

let field_proj_tm = (

let uu____8035 = (

let uu____8036 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____8036))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8035 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) FStar_Pervasives_Native.None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____8050 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____8059 -> (match (uu____8059) with
| (x, uu____8064) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____8066 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____8066) with
| (field_name, uu____8071) -> begin
(

let t = (

let uu____8073 = (

let uu____8074 = (

let uu____8077 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____8077))
in (FStar_Syntax_Util.arrow binders uu____8074))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____8073))
in (

let only_decl = (((

let uu____8079 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____8079)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____8080 = (

let uu____8081 = (FStar_TypeChecker_Env.current_module env)
in uu____8081.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____8080)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____8091 = (FStar_List.filter (fun uu___113_8093 -> (match (uu___113_8093) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____8094 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____8091)
end
| uu____8095 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___114_8102 -> (match (uu___114_8102) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____8103 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta}
in ((

let uu____8106 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8106) with
| true -> begin
(

let uu____8107 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____8107))
end
| uu____8108 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____8110 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____8134 -> (match (uu____8134) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match (((i + ntps) = j)) with
| true -> begin
(

let uu____8150 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____8150), (b)))
end
| uu____8155 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____8162 = (

let uu____8165 = (

let uu____8166 = (

let uu____8171 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____8171), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____8166))
in (pos uu____8165))
in ((uu____8162), (b)))
end
| uu____8174 -> begin
(

let uu____8175 = (

let uu____8178 = (

let uu____8179 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8179))
in (pos uu____8178))
in ((uu____8175), (b)))
end)
end))
end))))
in (

let pat = (

let uu____8191 = (

let uu____8194 = (

let uu____8195 = (

let uu____8203 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____8203), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____8195))
in (pos uu____8194))
in (

let uu____8209 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____8191), (FStar_Pervasives_Native.None), (uu____8209))))
in (

let body = (

let uu____8220 = (

let uu____8223 = (

let uu____8224 = (

let uu____8240 = (

let uu____8242 = (FStar_Syntax_Util.branch pat)
in (uu____8242)::[])
in ((arg_exp), (uu____8240)))
in FStar_Syntax_Syntax.Tm_match (uu____8224))
in (FStar_Syntax_Syntax.mk uu____8223))
in (uu____8220 FStar_Pervasives_Native.None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let dd = (

let uu____8259 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____8259) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____8261 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____8263 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____8265 = (

let uu____8268 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____8268))
in (

let uu____8269 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____8265; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____8269}))
in (

let impl = (

let uu____8273 = (

let uu____8274 = (

let uu____8280 = (

let uu____8282 = (

let uu____8283 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____8283 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____8282)::[])
in ((((false), ((lb)::[]))), (uu____8280), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____8274))
in {FStar_Syntax_Syntax.sigel = uu____8273; FStar_Syntax_Syntax.sigrng = p1; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta})
in ((

let uu____8298 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8298) with
| true -> begin
(

let uu____8299 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____8299))
end
| uu____8300 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____8302 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
)))))))
end)))
end))))
in (FStar_All.pipe_right uu____8050 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, uu____8329) when (not ((FStar_Ident.lid_equals constr_lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____8332 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____8332) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____8345 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____8345) with
| (formals, uu____8355) -> begin
(

let uu____8366 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____8379 = (

let uu____8380 = (

let uu____8381 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____8381))
in (FStar_Ident.lid_equals typ_lid uu____8380))
in (match (uu____8379) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____8391, uvs', tps, typ0, uu____8395, constrs) -> begin
FStar_Pervasives_Native.Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____8408 -> begin
(failwith "Impossible")
end)
end
| uu____8413 -> begin
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
| uu____8440 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____8366) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____8450 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____8450) with
| (indices, uu____8460) -> begin
(

let refine_domain = (

let uu____8472 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___115_8474 -> (match (uu___115_8474) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8475) -> begin
true
end
| uu____8480 -> begin
false
end))))
in (match (uu____8472) with
| true -> begin
false
end
| uu____8481 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___116_8487 -> (match (uu___116_8487) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8489, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____8496 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____8497 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____8497) with
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
| uu____8503 -> begin
iquals
end)
in (

let fields = (

let uu____8505 = (FStar_Util.first_N n_typars formals)
in (match (uu____8505) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____8536 uu____8537 -> (match (((uu____8536), (uu____8537))) with
| ((x, uu____8547), (x', uu____8549)) -> begin
(

let uu____8554 = (

let uu____8559 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____8559)))
in FStar_Syntax_Syntax.NT (uu____8554))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____8560 -> begin
[]
end))




