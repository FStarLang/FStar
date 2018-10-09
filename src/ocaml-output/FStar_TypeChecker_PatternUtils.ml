
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let rec elaborate_pat : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.pat = (fun env p -> (

let maybe_dot = (fun inaccessible a r -> (match (inaccessible) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) r)
end
| uu____39 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) r)
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____77 -> (match (uu____77) with
| (p1, imp) -> begin
(

let uu____88 = (elaborate_pat env p1)
in ((uu____88), (imp)))
end)) pats)
in (

let uu____89 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____89) with
| (uu____94, t) -> begin
(

let uu____96 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____96) with
| (f, uu____112) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____242)::uu____243) -> begin
(

let uu____286 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_TooManyPatternArguments), ("Too many pattern arguments")) uu____286))
end
| ((uu____295)::uu____296, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____374 -> (match (uu____374) with
| (t1, imp) -> begin
(match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____401 = (

let uu____404 = (FStar_Syntax_Syntax.range_of_bv t1)
in FStar_Pervasives_Native.Some (uu____404))
in (FStar_Syntax_Syntax.new_bv uu____401 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____406 = (maybe_dot inaccessible a r)
in ((uu____406), (true)))))
end
| uu____411 -> begin
(

let uu____414 = (

let uu____419 = (

let uu____420 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____420))
in ((FStar_Errors.Fatal_InsufficientPatternArguments), (uu____419)))
in (

let uu____421 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error uu____414 uu____421)))
end)
end))))
end
| ((f1)::formals', ((p1, p_imp))::pats') -> begin
(match (f1) with
| (uu____495, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) when (inaccessible && p_imp) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____507) -> begin
(

let uu____514 = (aux formals' pats')
in (((p1), (true)))::uu____514)
end
| FStar_Syntax_Syntax.Pat_wild (uu____531) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p2 = (

let uu____536 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (maybe_dot inaccessible a uu____536))
in (

let uu____537 = (aux formals' pats')
in (((p2), (true)))::uu____537)))
end
| uu____554 -> begin
(

let uu____555 = (

let uu____560 = (

let uu____561 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "This pattern (%s) binds an inaccesible argument; use a wildcard (\'_\') pattern" uu____561))
in ((FStar_Errors.Fatal_InsufficientPatternArguments), (uu____560)))
in (FStar_Errors.raise_error uu____555 p1.FStar_Syntax_Syntax.p))
end)
end
| (uu____570, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____571))) when p_imp -> begin
(

let uu____574 = (aux formals' pats')
in (((p1), (true)))::uu____574)
end
| (uu____591, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p2 = (

let uu____599 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (maybe_dot inaccessible a uu____599))
in (

let uu____600 = (aux formals' pats2)
in (((p2), (true)))::uu____600)))
end
| (uu____617, imp) -> begin
(

let uu____623 = (

let uu____630 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p1), (uu____630)))
in (

let uu____633 = (aux formals' pats')
in (uu____623)::uu____633))
end)
end))
in (

let uu___266_648 = p
in (

let uu____649 = (

let uu____650 = (

let uu____663 = (aux f pats1)
in ((fv), (uu____663)))
in FStar_Syntax_Syntax.Pat_cons (uu____650))
in {FStar_Syntax_Syntax.v = uu____649; FStar_Syntax_Syntax.p = uu___266_648.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____680 -> begin
p
end)))


let pat_as_exp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.pat) = (fun introduce_bv_uvars env p -> (

let intro_bv = (fun env1 x -> (match ((not (introduce_bv_uvars))) with
| true -> begin
(((

let uu___267_740 = x
in {FStar_Syntax_Syntax.ppname = uu___267_740.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___267_740.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun})), (FStar_TypeChecker_Env.trivial_guard), (env1))
end
| uu____741 -> begin
(

let uu____742 = (FStar_Syntax_Util.type_u ())
in (match (uu____742) with
| (t, uu____754) -> begin
(

let uu____755 = (

let uu____768 = (FStar_Syntax_Syntax.range_of_bv x)
in (FStar_TypeChecker_Env.new_implicit_var_aux "pattern bv type" uu____768 env1 t FStar_Syntax_Syntax.Allow_untyped))
in (match (uu____755) with
| (t_x, uu____776, guard) -> begin
(

let x1 = (

let uu___268_791 = x
in {FStar_Syntax_Syntax.ppname = uu___268_791.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___268_791.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})
in (

let uu____792 = (FStar_TypeChecker_Env.push_bv env1 x1)
in ((x1), (guard), (uu____792))))
end))
end))
end))
in (

let rec pat_as_arg_with_env = (fun env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = (match (c) with
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(FStar_ToSyntax_ToSyntax.desugar_machine_integer env1.FStar_TypeChecker_Env.dsenv repr sw p1.FStar_Syntax_Syntax.p)
end
| uu____862 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
end)
in (([]), ([]), ([]), (env1), (e), (FStar_TypeChecker_Env.trivial_guard), (p1)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____870) -> begin
(

let uu____875 = (FStar_Syntax_Util.type_u ())
in (match (uu____875) with
| (k, uu____901) -> begin
(

let uu____902 = (

let uu____915 = (FStar_Syntax_Syntax.range_of_bv x)
in (FStar_TypeChecker_Env.new_implicit_var_aux "pat_dot_term type" uu____915 env1 k FStar_Syntax_Syntax.Allow_untyped))
in (match (uu____902) with
| (t, uu____937, g) -> begin
(

let x1 = (

let uu___269_952 = x
in {FStar_Syntax_Syntax.ppname = uu___269_952.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___269_952.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____953 = (

let uu____966 = (FStar_Syntax_Syntax.range_of_bv x1)
in (FStar_TypeChecker_Env.new_implicit_var_aux "pat_dot_term" uu____966 env1 t FStar_Syntax_Syntax.Allow_untyped))
in (match (uu____953) with
| (e, uu____988, g') -> begin
(

let p2 = (

let uu___270_1005 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.p = uu___270_1005.FStar_Syntax_Syntax.p})
in (

let uu____1008 = (FStar_TypeChecker_Env.conj_guard g g')
in (([]), ([]), ([]), (env1), (e), (uu____1008), (p2))))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____1016 = (intro_bv env1 x)
in (match (uu____1016) with
| (x1, g, env2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (g), (p1)))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____1056 = (intro_bv env1 x)
in (match (uu____1056) with
| (x1, g, env2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ((x1)::[]), ([]), (env2), (e), (g), (p1)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1113 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1247 uu____1248 -> (match (((uu____1247), (uu____1248))) with
| ((b, a, w, env2, args, guard, pats1), (p2, imp)) -> begin
(

let uu____1446 = (pat_as_arg_with_env env2 p2)
in (match (uu____1446) with
| (b', a', w', env3, te, guard', pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1521 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (

let uu____1522 = (FStar_TypeChecker_Env.conj_guard guard guard')
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), (uu____1522), ((((pat), (imp)))::pats1))))
end))
end)) (([]), ([]), ([]), (env1), ([]), (FStar_TypeChecker_Env.trivial_guard), ([]))))
in (match (uu____1113) with
| (b, a, w, env2, args, guard, pats1) -> begin
(

let e = (

let uu____1653 = (

let uu____1658 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____1659 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____1658 uu____1659)))
in (uu____1653 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in (

let uu____1664 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____1675 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____1686 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____1664), (uu____1675), (uu____1686), (env2), (e), (guard), ((

let uu___271_1704 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___271_1704.FStar_Syntax_Syntax.p})))))))
end))
end))
in (

let one_pat = (fun env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____1747 = (pat_as_arg_with_env env1 p2)
in (match (uu____1747) with
| (b, a, w, env2, arg, guard, p3) -> begin
(

let uu____1805 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____1805) with
| FStar_Pervasives_Native.Some (x) -> begin
(

let m = (FStar_Syntax_Print.bv_to_string x)
in (

let err = (

let uu____1837 = (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)
in ((FStar_Errors.Fatal_NonLinearPatternVars), (uu____1837)))
in (FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p)))
end
| uu____1856 -> begin
((b), (a), (w), (arg), (guard), (p3))
end))
end))))
in (

let uu____1865 = (one_pat env p)
in (match (uu____1865) with
| (b, uu____1895, uu____1896, tm, guard, p1) -> begin
((b), (tm), (guard), (p1))
end))))))




