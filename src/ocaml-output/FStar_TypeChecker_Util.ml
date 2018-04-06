
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (

let uu____17 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____18 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.log_issue uu____17 uu____18))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____26 = (

let uu____27 = (FStar_Syntax_Subst.compress t)
in uu____27.FStar_Syntax_Syntax.n)
in (match (uu____26) with
| FStar_Syntax_Syntax.Tm_type (uu____30) -> begin
true
end
| uu____31 -> begin
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

let uu____73 = ((FStar_Options.full_context_dependency ()) || (

let uu____75 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____75)))
in (match (uu____73) with
| true -> begin
(FStar_TypeChecker_Env.all_binders env)
end
| uu____76 -> begin
(t_binders env)
end))
in (

let uu____77 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar uu____77 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (

let uu____84 = (new_uvar_aux env k)
in (FStar_Pervasives_Native.fst uu____84)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___83_93 -> (match (uu___83_93) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, uu____95); FStar_Syntax_Syntax.pos = uu____96; FStar_Syntax_Syntax.vars = uu____97} -> begin
uv
end
| uu____124 -> begin
(failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (

let uu____149 = (FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid)
in (match (uu____149) with
| FStar_Pervasives_Native.Some ((uu____172)::((tm, uu____174))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| uu____226 -> begin
(

let uu____237 = (new_uvar_aux env k)
in (match (uu____237) with
| (t, u) -> begin
(

let g = (

let uu___107_257 = FStar_TypeChecker_Rel.trivial_guard
in (

let uu____258 = (

let uu____273 = (

let uu____286 = (as_uvar u)
in ((reason), (env), (uu____286), (t), (k), (r)))
in (uu____273)::[])
in {FStar_TypeChecker_Env.guard_f = uu___107_257.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___107_257.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___107_257.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____258}))
in (

let uu____311 = (

let uu____318 = (

let uu____323 = (as_uvar u)
in ((uu____323), (r)))
in (uu____318)::[])
in ((t), (uu____311), (g))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____351 = (

let uu____352 = (FStar_Util.set_is_empty uvs)
in (not (uu____352)))
in (match (uu____351) with
| true -> begin
(

let us = (

let uu____358 = (

let uu____361 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun uu____379 -> (match (uu____379) with
| (x, uu____385) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) uu____361))
in (FStar_All.pipe_right uu____358 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____392 = (

let uu____397 = (

let uu____398 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____398))
in ((FStar_Errors.Error_UncontrainedUnificationVar), (uu____397)))
in (FStar_Errors.log_issue r uu____392));
(FStar_Options.pop ());
))
end
| uu____399 -> begin
()
end))))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____411 -> (match (uu____411) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____421; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____423; FStar_Syntax_Syntax.lbpos = uu____424} -> begin
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
| uu____460 -> begin
()
end);
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder1 = (fun scope a -> (

let uu____473 = (

let uu____474 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in uu____474.FStar_Syntax_Syntax.n)
in (match (uu____473) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____481 = (FStar_Syntax_Util.type_u ())
in (match (uu____481) with
| (k, uu____491) -> begin
(

let t2 = (

let uu____493 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right uu____493 FStar_Pervasives_Native.fst))
in (((

let uu___108_503 = a
in {FStar_Syntax_Syntax.ppname = uu___108_503.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___108_503.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (false)))
end))
end
| uu____504 -> begin
((a), (true))
end)))
in (

let rec aux = (fun must_check_ty vars e1 -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e3, uu____541) -> begin
(aux must_check_ty vars e3)
end
| FStar_Syntax_Syntax.Tm_ascribed (e3, t2, uu____548) -> begin
(((FStar_Pervasives_Native.fst t2)), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____611) -> begin
(

let uu____632 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____692 uu____693 -> (match (((uu____692), (uu____693))) with
| ((scope, bs1, must_check_ty1), (a, imp)) -> begin
(

let uu____771 = (match (must_check_ty1) with
| true -> begin
((a), (true))
end
| uu____780 -> begin
(mk_binder1 scope a)
end)
in (match (uu____771) with
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
in (match (uu____632) with
| (scope, bs1, must_check_ty1) -> begin
(

let uu____883 = (aux must_check_ty1 scope body)
in (match (uu____883) with
| (res, must_check_ty2) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____912 = (FStar_Options.ml_ish ())
in (match (uu____912) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____913 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Util.arrow bs1 c)
in ((

let uu____919 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____919) with
| true -> begin
(

let uu____920 = (FStar_Range.string_of_range r)
in (

let uu____921 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____922 = (FStar_Util.string_of_bool must_check_ty2)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" uu____920 uu____921 uu____922))))
end
| uu____923 -> begin
()
end));
((FStar_Util.Inl (t2)), (must_check_ty2));
)))
end))
end))
end
| uu____932 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end
| uu____945 -> begin
(

let uu____946 = (

let uu____951 = (

let uu____952 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____952 FStar_Pervasives_Native.fst))
in FStar_Util.Inl (uu____951))
in ((uu____946), (false)))
end)
end)))
in (

let uu____965 = (

let uu____974 = (t_binders env)
in (aux false uu____974 e))
in (match (uu____965) with
| (t2, b) -> begin
(

let t3 = (match (t2) with
| FStar_Util.Inr (c) -> begin
(

let uu____999 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____999) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1002 -> begin
(

let uu____1003 = (

let uu____1008 = (

let uu____1009 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____1009))
in ((FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec), (uu____1008)))
in (FStar_Errors.raise_error uu____1003 rng))
end))
end
| FStar_Util.Inl (t3) -> begin
t3
end)
in (([]), (t3), (b)))
end)))));
)
end
| uu____1017 -> begin
(

let uu____1018 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____1018) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let pat_as_exp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p tc_annot -> (

let check_bv = (fun env1 x -> (

let uu____1098 = (

let uu____1103 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in (match (uu____1103) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____1108; FStar_Syntax_Syntax.vars = uu____1109} -> begin
(

let uu____1112 = (FStar_Syntax_Util.type_u ())
in (match (uu____1112) with
| (t, uu____1122) -> begin
(

let uu____1123 = (new_uvar env1 t)
in ((uu____1123), (FStar_TypeChecker_Rel.trivial_guard)))
end))
end
| t -> begin
(tc_annot env1 t)
end))
in (match (uu____1098) with
| (t_x, guard) -> begin
(((

let uu___109_1132 = x
in {FStar_Syntax_Syntax.ppname = uu___109_1132.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___109_1132.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (guard))
end)))
in (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = (match (c) with
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(FStar_ToSyntax_ToSyntax.desugar_machine_integer env1.FStar_TypeChecker_Env.dsenv repr sw p1.FStar_Syntax_Syntax.p)
end
| uu____1201 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
end)
in (([]), ([]), ([]), (env1), (e), (FStar_TypeChecker_Rel.trivial_guard), (p1)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____1209) -> begin
(

let uu____1214 = (FStar_Syntax_Util.type_u ())
in (match (uu____1214) with
| (k, uu____1240) -> begin
(

let t = (new_uvar env1 k)
in (

let x1 = (

let uu___110_1243 = x
in {FStar_Syntax_Syntax.ppname = uu___110_1243.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_1243.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____1244 = (

let uu____1249 = (FStar_TypeChecker_Env.all_binders env1)
in (FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p uu____1249 t))
in (match (uu____1244) with
| (e, u) -> begin
(

let p2 = (

let uu___111_1275 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.p = uu___111_1275.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env1), (e), (FStar_TypeChecker_Rel.trivial_guard), (p2)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____1285 = (check_bv env1 x)
in (match (uu____1285) with
| (x1, g) -> begin
(

let env2 = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env1 x1)
end
| uu____1313 -> begin
env1
end)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (g), (p1))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____1326 = (check_bv env1 x)
in (match (uu____1326) with
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

let uu____1383 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1519 uu____1520 -> (match (((uu____1519), (uu____1520))) with
| ((b, a, w, env2, args, guard, pats1), (p2, imp)) -> begin
(

let uu____1718 = (pat_as_arg_with_env allow_wc_dependence env2 p2)
in (match (uu____1718) with
| (b', a', w', env3, te, guard', pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1793 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (

let uu____1794 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), (uu____1794), ((((pat), (imp)))::pats1))))
end))
end)) (([]), ([]), ([]), (env1), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([]))))
in (match (uu____1383) with
| (b, a, w, env2, args, guard, pats1) -> begin
(

let e = (

let uu____1925 = (

let uu____1926 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____1927 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____1926 uu____1927)))
in (uu____1925 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in (

let uu____1934 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____1945 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____1956 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____1934), (uu____1945), (uu____1956), (env2), (e), (guard), ((

let uu___112_1978 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___112_1978.FStar_Syntax_Syntax.p})))))))
end))
end))
in (

let rec elaborate_pat = (fun env1 p1 -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) r)
end
| uu____2016 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) r)
end))
in (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____2062 -> (match (uu____2062) with
| (p2, imp) -> begin
(

let uu____2081 = (elaborate_pat env1 p2)
in ((uu____2081), (imp)))
end)) pats)
in (

let uu____2086 = (FStar_TypeChecker_Env.lookup_datacon env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2086) with
| (uu____2093, t) -> begin
(

let uu____2095 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2095) with
| (f, uu____2111) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____2233)::uu____2234) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TooManyPatternArguments), ("Too many pattern arguments")) (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
end
| ((uu____2285)::uu____2286, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____2364 -> (match (uu____2364) with
| (t1, imp) -> begin
(match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____2391 = (

let uu____2394 = (FStar_Syntax_Syntax.range_of_bv t1)
in FStar_Pervasives_Native.Some (uu____2394))
in (FStar_Syntax_Syntax.new_bv uu____2391 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2396 = (maybe_dot inaccessible a r)
in ((uu____2396), (true)))))
end
| uu____2401 -> begin
(

let uu____2404 = (

let uu____2409 = (

let uu____2410 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____2410))
in ((FStar_Errors.Fatal_InsufficientPatternArguments), (uu____2409)))
in (FStar_Errors.raise_error uu____2404 (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end)
end))))
end
| ((f1)::formals', ((p2, p_imp))::pats') -> begin
(match (f1) with
| (uu____2484, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____2485))) when p_imp -> begin
(

let uu____2488 = (aux formals' pats')
in (((p2), (true)))::uu____2488)
end
| (uu____2505, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p2.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p3 = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (

let uu____2513 = (aux formals' pats2)
in (((p3), (true)))::uu____2513)))
end
| (uu____2530, imp) -> begin
(

let uu____2536 = (

let uu____2543 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p2), (uu____2543)))
in (

let uu____2546 = (aux formals' pats')
in (uu____2536)::uu____2546))
end)
end))
in (

let uu___113_2561 = p1
in (

let uu____2564 = (

let uu____2565 = (

let uu____2578 = (aux f pats1)
in ((fv), (uu____2578)))
in FStar_Syntax_Syntax.Pat_cons (uu____2565))
in {FStar_Syntax_Syntax.v = uu____2564; FStar_Syntax_Syntax.p = uu___113_2561.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____2595 -> begin
p1
end)))
in (

let one_pat = (fun allow_wc_dependence env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____2631 = (pat_as_arg_with_env allow_wc_dependence env1 p2)
in (match (uu____2631) with
| (b, a, w, env2, arg, guard, p3) -> begin
(

let uu____2689 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____2689) with
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2715 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in (FStar_Errors.raise_error uu____2715 p3.FStar_Syntax_Syntax.p))
end
| uu____2738 -> begin
((b), (a), (w), (arg), (guard), (p3))
end))
end))))
in (

let uu____2747 = (one_pat true env p)
in (match (uu____2747) with
| (b, uu____2777, uu____2778, tm, guard, p1) -> begin
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
| (uu____2824, FStar_Syntax_Syntax.Tm_uinst (e2, uu____2826)) -> begin
(aux p1 e2)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____2831), uu____2832) -> begin
(pkg p1.FStar_Syntax_Syntax.v)
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____2836 = (

let uu____2837 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2838 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2837 uu____2838)))
in (failwith uu____2836))
end
| uu____2839 -> begin
()
end);
(

let uu____2841 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____2841) with
| true -> begin
(

let uu____2842 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2843 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____2842 uu____2843)))
end
| uu____2844 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___114_2847 = x
in {FStar_Syntax_Syntax.ppname = uu___114_2847.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_2847.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____2851 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____2851) with
| true -> begin
(

let uu____2852 = (

let uu____2853 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2854 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2853 uu____2854)))
in (failwith uu____2852))
end
| uu____2855 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___115_2858 = x
in {FStar_Syntax_Syntax.ppname = uu___115_2858.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_2858.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____2860), uu____2861) -> begin
(pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e1)))))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____2883 = (

let uu____2884 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____2884)))
in (match (uu____2883) with
| true -> begin
(

let uu____2885 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2885))
end
| uu____2886 -> begin
()
end));
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____2904; FStar_Syntax_Syntax.vars = uu____2905}, args)) -> begin
((

let uu____2944 = (

let uu____2945 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____2945 Prims.op_Negation))
in (match (uu____2944) with
| true -> begin
(

let uu____2946 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2946))
end
| uu____2947 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____3082))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3157)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3194) -> begin
(

let pat = (

let uu____3216 = (aux argpat e2)
in (

let uu____3217 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3216), (uu____3217))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3222 -> begin
(

let uu____3245 = (

let uu____3246 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3247 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3246 uu____3247)))
in (failwith uu____3245))
end))
in (match_args [] args argpats)));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____3259; FStar_Syntax_Syntax.vars = uu____3260}, uu____3261); FStar_Syntax_Syntax.pos = uu____3262; FStar_Syntax_Syntax.vars = uu____3263}, args)) -> begin
((

let uu____3306 = (

let uu____3307 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____3307 Prims.op_Negation))
in (match (uu____3306) with
| true -> begin
(

let uu____3308 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3308))
end
| uu____3309 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____3444))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3519)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3556) -> begin
(

let pat = (

let uu____3578 = (aux argpat e2)
in (

let uu____3579 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3578), (uu____3579))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3584 -> begin
(

let uu____3607 = (

let uu____3608 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3609 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3608 uu____3609)))
in (failwith uu____3607))
end))
in (match_args [] args argpats)));
)
end
| uu____3618 -> begin
(

let uu____3623 = (

let uu____3624 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____3625 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____3626 = (FStar_Syntax_Print.term_to_string exp)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____3624 uu____3625 uu____3626))))
in (failwith uu____3623))
end))))
in (aux p exp))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____3663 -> (match (uu____3663) with
| (p, i) -> begin
(

let uu____3680 = (decorated_pattern_as_term p)
in (match (uu____3680) with
| (vars, te) -> begin
(

let uu____3703 = (

let uu____3708 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____3708)))
in ((vars), (uu____3703)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____3722 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____3722)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____3726 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____3726)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____3730 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____3730)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3751 = (

let uu____3766 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____3766 FStar_List.unzip))
in (match (uu____3751) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____3876 = (

let uu____3877 = (

let uu____3878 = (

let uu____3893 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____3893), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____3878))
in (mk1 uu____3877))
in ((vars1), (uu____3876))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let comp_univ_opt : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____3923, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.GTotal (uu____3933, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::uu____3947 -> begin
FStar_Pervasives_Native.Some (hd1)
end)
end))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____3971))::[] -> begin
wp
end
| uu____3988 -> begin
(

let uu____3997 = (

let uu____3998 = (

let uu____3999 = (FStar_List.map (fun uu____4009 -> (match (uu____4009) with
| (x, uu____4015) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____3999 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____3998))
in (failwith uu____3997))
end)
in (

let uu____4020 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____4020), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____4034 = (destruct_comp c)
in (match (uu____4034) with
| (u, uu____4042, wp) -> begin
(

let uu____4044 = (

let uu____4053 = (

let uu____4054 = (lift.FStar_TypeChecker_Env.mlift_wp u c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____4054))
in (uu____4053)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____4044; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____4064 = (

let uu____4071 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____4072 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____4071 uu____4072)))
in (match (uu____4064) with
| (m, uu____4074, uu____4075) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____4085 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____4085) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____4086 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____4122 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____4122) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____4159 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____4159) with
| (a, kwp) -> begin
(

let uu____4190 = (destruct_comp m1)
in (

let uu____4197 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____4190), (uu____4197))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags1 -> (

let uu____4259 = (

let uu____4260 = (

let uu____4269 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4269)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____4260; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp uu____4259)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags1 -> (match ((FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____4301 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1)
end))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu____4308 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4308 lc.FStar_Syntax_Syntax.cflags (fun uu____4311 -> (

let uu____4312 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Subst.subst_comp subst1 uu____4312))))))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4316 = (

let uu____4317 = (FStar_Syntax_Subst.compress t)
in uu____4317.FStar_Syntax_Syntax.n)
in (match (uu____4316) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4320) -> begin
true
end
| uu____4333 -> begin
false
end)))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (reason1) -> begin
(

let uu____4371 = (

let uu____4372 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____4372))
in (match (uu____4371) with
| true -> begin
f
end
| uu____4373 -> begin
(

let uu____4374 = (reason1 ())
in (label uu____4374 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___116_4385 = g
in (

let uu____4386 = (

let uu____4387 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____4387))
in {FStar_TypeChecker_Env.guard_f = uu____4386; FStar_TypeChecker_Env.deferred = uu___116_4385.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___116_4385.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___116_4385.FStar_TypeChecker_Env.implicits}))
end))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____4401 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4401) with
| true -> begin
c
end
| uu____4402 -> begin
(

let uu____4403 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4403) with
| true -> begin
c
end
| uu____4404 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____4442 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4442)::[])
in (

let us = (

let uu____4446 = (

let uu____4449 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____4449)::[])
in (u_res)::uu____4446)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____4453 = (

let uu____4454 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____4455 = (

let uu____4456 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4457 = (

let uu____4460 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____4461 = (

let uu____4464 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____4464)::[])
in (uu____4460)::uu____4461))
in (uu____4456)::uu____4457))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4454 uu____4455)))
in (uu____4453 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4468 = (destruct_comp c1)
in (match (uu____4468) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end)))


let close_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____4495 -> (

let uu____4496 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (close_comp env bvs uu____4496)))))


let should_not_inline_lc : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___84_4503 -> (match (uu___84_4503) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____4504 -> begin
false
end)))))


let should_return : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun env eopt lc -> (match (eopt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (e) -> begin
((((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) && (

let uu____4520 = (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____4520)))) && (

let uu____4527 = (FStar_Syntax_Util.head_and_args' e)
in (match (uu____4527) with
| (head1, uu____4541) -> begin
(

let uu____4558 = (

let uu____4559 = (FStar_Syntax_Util.un_uinst head1)
in uu____4559.FStar_Syntax_Syntax.n)
in (match (uu____4558) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____4563 = (

let uu____4564 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_irreducible env uu____4564))
in (not (uu____4563)))
end
| uu____4565 -> begin
true
end))
end))) && (

let uu____4567 = (should_not_inline_lc lc)
in (not (uu____4567))))
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env u_t_opt t v1 -> (

let c = (

let uu____4585 = (

let uu____4586 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____4586))
in (match (uu____4585) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____4587 -> begin
(

let uu____4588 = (FStar_Syntax_Util.is_unit t)
in (match (uu____4588) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero)))
end
| uu____4589 -> begin
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

let uu____4594 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4594) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____4595 -> begin
(

let uu____4596 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____4596) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____4604 = (

let uu____4605 = (

let uu____4606 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____4607 = (

let uu____4608 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____4609 = (

let uu____4612 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____4612)::[])
in (uu____4608)::uu____4609))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4606 uu____4607)))
in (uu____4605 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env uu____4604)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
end))
in ((

let uu____4616 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____4616) with
| true -> begin
(

let uu____4617 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____4618 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____4619 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4617 uu____4618 uu____4619))))
end
| uu____4620 -> begin
()
end));
c;
)))


let weaken_flags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags1 -> (

let uu____4630 = (FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___85_4634 -> (match (uu___85_4634) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____4635 -> begin
false
end))))
in (match (uu____4630) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____4638 -> begin
(FStar_All.pipe_right flags1 (FStar_List.collect (fun uu___86_4644 -> (match (uu___86_4644) with
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

let uu____4657 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4657) with
| true -> begin
c
end
| uu____4658 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4660 = (destruct_comp c1)
in (match (uu____4660) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____4674 = (

let uu____4675 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____4676 = (

let uu____4677 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4678 = (

let uu____4681 = (FStar_Syntax_Syntax.as_arg formula)
in (

let uu____4682 = (

let uu____4685 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4685)::[])
in (uu____4681)::uu____4682))
in (uu____4677)::uu____4678))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4675 uu____4676)))
in (uu____4674 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (

let uu____4688 = (weaken_flags c1.FStar_Syntax_Syntax.flags)
in (mk_comp md u_res_t res_t wp1 uu____4688))))
end)))
end)))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____4703 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let uu____4705 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4705) with
| true -> begin
c
end
| uu____4706 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(weaken_comp env c f1)
end)
end))))
in (

let uu____4708 = (weaken_flags lc.FStar_Syntax_Syntax.cflags)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ uu____4708 weaken))))


let strengthen_comp : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun env reason c f flags1 -> (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____4739 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4741 = (destruct_comp c1)
in (match (uu____4741) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____4755 = (

let uu____4756 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____4757 = (

let uu____4758 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4759 = (

let uu____4762 = (

let uu____4763 = (

let uu____4764 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____4764 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____4763))
in (

let uu____4765 = (

let uu____4768 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4768)::[])
in (uu____4762)::uu____4765))
in (uu____4758)::uu____4759))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4756 uu____4757)))
in (uu____4755 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 flags1)))
end)))
end))


let strengthen_precondition : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e_for_debug_only lc g0 -> (

let uu____4803 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____4803) with
| true -> begin
((lc), (g0))
end
| uu____4808 -> begin
(

let flags1 = (

let uu____4812 = (

let uu____4819 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____4819) with
| true -> begin
((true), ((FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]))
end
| uu____4828 -> begin
((false), ([]))
end))
in (match (uu____4812) with
| (maybe_trivial_post, flags1) -> begin
(

let uu____4839 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___87_4847 -> (match (uu___87_4847) with
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
| uu____4850 -> begin
[]
end))))
in (FStar_List.append flags1 uu____4839))
end))
in (

let strengthen = (fun uu____4854 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____4856 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____4858 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____4858) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____4861 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4861) with
| true -> begin
(

let uu____4862 = (FStar_TypeChecker_Normalize.term_to_string env e_for_debug_only)
in (

let uu____4863 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____4862 uu____4863)))
end
| uu____4864 -> begin
()
end));
(strengthen_comp env reason c f flags1);
)
end)))
end)))
in (

let uu____4865 = (

let uu____4866 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____4866 lc.FStar_Syntax_Syntax.res_typ flags1 strengthen))
in ((uu____4865), ((

let uu___117_4868 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___117_4868.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___117_4868.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___117_4868.FStar_TypeChecker_Env.implicits}))))))
end)))


let lcomp_has_trivial_postcondition : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) || (FStar_Util.for_some (fun uu___88_4873 -> (match (uu___88_4873) with
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
true
end
| uu____4874 -> begin
false
end)) lc.FStar_Syntax_Syntax.cflags)))


let maybe_add_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env uopt lc e -> (

let uu____4891 = ((FStar_Syntax_Util.is_lcomp_partial_return lc) || env.FStar_TypeChecker_Env.lax)
in (match (uu____4891) with
| true -> begin
e
end
| uu____4892 -> begin
(

let uu____4893 = ((lcomp_has_trivial_postcondition lc) && (

let uu____4895 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____4895)))
in (match (uu____4893) with
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
| uu____4916 -> begin
e
end))
end)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____4933 -> (match (uu____4933) with
| (b, lc2) -> begin
(

let debug1 = (fun f -> (

let uu____4951 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4951) with
| true -> begin
(f ())
end
| uu____4952 -> begin
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

let uu____4959 = ((should_not_inline_lc lc11) || (should_not_inline_lc lc21))
in (match (uu____4959) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____4962 -> begin
(

let flags1 = (

let uu____4966 = (FStar_Syntax_Util.is_total_lcomp lc11)
in (match (uu____4966) with
| true -> begin
(

let uu____4969 = (FStar_Syntax_Util.is_total_lcomp lc21)
in (match (uu____4969) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____4972 -> begin
(

let uu____4973 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
in (match (uu____4973) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____4976 -> begin
[]
end))
end))
end
| uu____4977 -> begin
(

let uu____4978 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) && (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21))
in (match (uu____4978) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____4981 -> begin
[]
end))
end))
in (

let uu____4982 = (lcomp_has_trivial_postcondition lc21)
in (match (uu____4982) with
| true -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::flags1
end
| uu____4985 -> begin
flags1
end)))
end))
in (

let bind_it = (fun uu____4989 -> (

let uu____4990 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4990) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____4992 -> begin
(

let c1 = (FStar_Syntax_Syntax.lcomp_comp lc11)
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp lc21)
in ((debug1 (fun uu____5004 -> (

let uu____5005 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____5006 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____5008 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n" uu____5005 uu____5006 uu____5008))))));
(

let aux = (fun uu____5020 -> (

let uu____5021 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____5021) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____5042) -> begin
(

let uu____5043 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____5043) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____5056 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____5061 -> begin
(

let uu____5062 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____5062) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____5075 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun e1opt1 reason -> (match (((e1opt1), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____5129 = (

let uu____5134 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____5134), (reason)))
in FStar_Util.Inl (uu____5129))
end
| uu____5141 -> begin
(aux ())
end))
in (

let try_simplify = (fun uu____5163 -> (

let rec maybe_close = (fun t x c -> (

let uu____5174 = (

let uu____5175 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in uu____5175.FStar_Syntax_Syntax.n)
in (match (uu____5174) with
| FStar_Syntax_Syntax.Tm_refine (y, uu____5179) -> begin
(maybe_close y.FStar_Syntax_Syntax.sort x c)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____5185 -> begin
c
end)))
in (

let uu____5186 = (

let uu____5187 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____5187))
in (match (uu____5186) with
| true -> begin
(

let uu____5198 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____5198) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____5211 -> begin
(

let uu____5212 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonTrivialPreConditionInPrims), ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")) uu____5212))
end))
end
| uu____5221 -> begin
(

let uu____5222 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____5222) with
| true -> begin
(subst_c2 e1opt "both total")
end
| uu____5231 -> begin
(

let uu____5232 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____5232) with
| true -> begin
(

let uu____5241 = (

let uu____5246 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____5246), ("both gtot")))
in FStar_Util.Inl (uu____5241))
end
| uu____5251 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____5270 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____5272 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____5272))))
in (match (uu____5270) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___118_5283 = x
in {FStar_Syntax_Syntax.ppname = uu___118_5283.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_5283.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____5284 = (

let uu____5289 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____5289), ("c1 Tot")))
in FStar_Util.Inl (uu____5284))))
end
| uu____5294 -> begin
(aux ())
end))
end
| uu____5295 -> begin
(aux ())
end)
end))
end))
end))))
in (

let uu____5304 = (try_simplify ())
in (match (uu____5304) with
| FStar_Util.Inl (c, reason) -> begin
((debug1 (fun uu____5324 -> (

let uu____5325 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "(2) bind: Simplified (because %s) to\n\t%s\n" reason uu____5325))));
c;
)
end
| FStar_Util.Inr (reason) -> begin
((debug1 (fun uu____5334 -> (FStar_Util.print1 "(2) bind: Not simplified because %s\n" reason)));
(

let mk_bind = (fun c11 b1 c21 -> (

let uu____5349 = (lift_and_destruct env c11 c21)
in (match (uu____5349) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b1) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5406 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____5406)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____5408 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5408)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____5421 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____5422 = (

let uu____5425 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____5426 = (

let uu____5429 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____5430 = (

let uu____5433 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____5434 = (

let uu____5437 = (

let uu____5438 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____5438))
in (uu____5437)::[])
in (uu____5433)::uu____5434))
in (uu____5429)::uu____5430))
in (uu____5425)::uu____5426))
in (uu____5421)::uu____5422))
in (

let wp = (

let uu____5442 = (

let uu____5443 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____5443 wp_args))
in (uu____5442 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (mk_comp md u_t2 t2 wp bind_flags))))))
end)))
in (

let mk_seq = (fun c11 b1 c21 -> (

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in (

let uu____5462 = (FStar_TypeChecker_Env.join env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____5462) with
| (m, uu____5470, lift2) -> begin
(

let c23 = (

let uu____5473 = (lift_comp c22 m lift2)
in (FStar_Syntax_Syntax.mk_Comp uu____5473))
in (

let uu____5474 = (destruct_comp c12)
in (match (uu____5474) with
| (u1, t1, wp1) -> begin
(

let md_pure_or_ghost = (FStar_TypeChecker_Env.get_effect_decl env c12.FStar_Syntax_Syntax.effect_name)
in (

let vc1 = (

let uu____5488 = (

let uu____5489 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u1)::[]) env md_pure_or_ghost md_pure_or_ghost.FStar_Syntax_Syntax.trivial)
in (

let uu____5490 = (

let uu____5491 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____5492 = (

let uu____5495 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____5495)::[])
in (uu____5491)::uu____5492))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5489 uu____5490)))
in (uu____5488 FStar_Pervasives_Native.None r1))
in (strengthen_comp env FStar_Pervasives_Native.None c23 vc1 bind_flags)))
end)))
end)))))
in (

let c1_typ = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____5501 = (destruct_comp c1_typ)
in (match (uu____5501) with
| (u_res_t1, res_t1, uu____5510) -> begin
(

let uu____5511 = ((FStar_Option.isSome b) && (should_return env e1opt lc11))
in (match (uu____5511) with
| true -> begin
(

let e1 = (FStar_Option.get e1opt)
in (

let x = (FStar_Option.get b)
in (

let uu____5514 = (FStar_Syntax_Util.is_partial_return c1)
in (match (uu____5514) with
| true -> begin
((debug1 (fun uu____5522 -> (

let uu____5523 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____5524 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case a): Substituting %s for %s" uu____5523 uu____5524)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (mk_bind c1 b c21));
)
end
| uu____5526 -> begin
(

let uu____5527 = (((FStar_Options.vcgen_optimize_bind_as_seq ()) && (lcomp_has_trivial_postcondition lc11)) && (

let uu____5529 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____5529)))
in (match (uu____5527) with
| true -> begin
(

let e1' = (

let uu____5551 = (FStar_Options.vcgen_decorate_with_type ())
in (match (uu____5551) with
| true -> begin
(FStar_Syntax_Util.mk_with_type u_res_t1 res_t1 e1)
end
| uu____5554 -> begin
e1
end))
in ((debug1 (fun uu____5562 -> (

let uu____5563 = (FStar_TypeChecker_Normalize.term_to_string env e1')
in (

let uu____5564 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case b): Substituting %s for %s" uu____5563 uu____5564)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1'))))::[]) c2)
in (mk_seq c1 b c21));
))
end
| uu____5568 -> begin
((debug1 (fun uu____5576 -> (

let uu____5577 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____5578 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case c): Adding equality %s = %s" uu____5577 uu____5578)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (

let x_eq_e = (

let uu____5581 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq2 u_res_t1 res_t1 e1 uu____5581))
in (

let c22 = (weaken_comp env c21 x_eq_e)
in (mk_bind c1 b c22))));
)
end))
end))))
end
| uu____5583 -> begin
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
| uu____5593 -> begin
g2
end))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let should_return1 = ((((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)) && (should_return env (FStar_Pervasives_Native.Some (e)) lc)) && (

let uu____5609 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____5609))))
in (

let flags1 = (match (should_return1) with
| true -> begin
(

let uu____5615 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____5615) with
| true -> begin
(FStar_Syntax_Syntax.RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____5618 -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end))
end
| uu____5619 -> begin
lc.FStar_Syntax_Syntax.cflags
end)
in (

let refine1 = (fun uu____5623 -> (

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

let uu____5627 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____5627) with
| true -> begin
(

let retc = (return_value env (FStar_Pervasives_Native.Some (u_t)) (FStar_Syntax_Util.comp_result c) e)
in (

let uu____5629 = (

let uu____5630 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____5630)))
in (match (uu____5629) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___119_5633 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___119_5633.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___119_5633.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___119_5633.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____5634 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags1)
end)))
end
| uu____5635 -> begin
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

let uu____5644 = (

let uu____5647 = (return_value env (FStar_Pervasives_Native.Some (u_t)) t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____5647 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5644))
in (

let eq1 = (FStar_Syntax_Util.mk_eq2 u_t t xexp e)
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____5652 = (

let uu____5653 = (

let uu____5654 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None uu____5654 ((FStar_Pervasives_Native.Some (x)), (eq_ret))))
in (FStar_Syntax_Syntax.lcomp_comp uu____5653))
in (FStar_Syntax_Util.comp_set_flags uu____5652 flags1))))))))))
end)))))
in (match ((not (should_return1))) with
| true -> begin
lc
end
| uu____5657 -> begin
(FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ flags1 refine1)
end)))))


let maybe_return_e2_and_bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r env e1opt lc1 e2 uu____5677 -> (match (uu____5677) with
| (x, lc2) -> begin
(

let lc21 = (

let eff1 = (FStar_TypeChecker_Env.norm_eff_name env lc1.FStar_Syntax_Syntax.eff_name)
in (

let eff2 = (FStar_TypeChecker_Env.norm_eff_name env lc2.FStar_Syntax_Syntax.eff_name)
in (

let uu____5689 = (((

let uu____5692 = (is_pure_or_ghost_effect env eff1)
in (not (uu____5692))) || (should_not_inline_lc lc1)) && (is_pure_or_ghost_effect env eff2))
in (match (uu____5689) with
| true -> begin
(maybe_assume_result_eq_pure_term env e2 lc2)
end
| uu____5693 -> begin
lc2
end))))
in (bind r env e1opt lc1 ((x), (lc21))))
end))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____5702 = (

let uu____5703 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____5703))
in (FStar_Syntax_Syntax.fvar uu____5702 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp)) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____5762 -> (match (uu____5762) with
| (uu____5775, eff_label, uu____5777, uu____5778) -> begin
(join_effects env eff eff_label)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let uu____5787 = (

let uu____5794 = (FStar_All.pipe_right lcases (FStar_Util.for_some (fun uu____5826 -> (match (uu____5826) with
| (uu____5839, uu____5840, flags1, uu____5842) -> begin
(FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___89_5854 -> (match (uu___89_5854) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____5855 -> begin
false
end))))
end))))
in (match (uu____5794) with
| true -> begin
((true), ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
end
| uu____5864 -> begin
((false), ([]))
end))
in (match (uu____5787) with
| (should_not_inline_whole_match, bind_cases_flags) -> begin
(

let bind_cases = (fun uu____5876 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____5878 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5878) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____5879 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____5898 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____5899 = (

let uu____5900 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____5901 = (

let uu____5902 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____5903 = (

let uu____5906 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____5907 = (

let uu____5910 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____5911 = (

let uu____5914 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____5914)::[])
in (uu____5910)::uu____5911))
in (uu____5906)::uu____5907))
in (uu____5902)::uu____5903))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5900 uu____5901)))
in (uu____5899 FStar_Pervasives_Native.None uu____5898))))
in (

let default_case = (

let post_k = (

let uu____5921 = (

let uu____5928 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____5928)::[])
in (

let uu____5929 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5921 uu____5929)))
in (

let kwp = (

let uu____5935 = (

let uu____5942 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____5942)::[])
in (

let uu____5943 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5935 uu____5943)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____5948 = (

let uu____5949 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____5949)::[])
in (

let uu____5950 = (

let uu____5951 = (

let uu____5954 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____5954))
in (

let uu____5955 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____5951 uu____5955)))
in (FStar_Syntax_Util.abs uu____5948 uu____5950 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let maybe_return = (fun eff_label_then cthen -> (

let uu____5971 = (should_not_inline_whole_match || (

let uu____5973 = (is_pure_or_ghost_effect env eff)
in (not (uu____5973))))
in (match (uu____5971) with
| true -> begin
(cthen true)
end
| uu____5974 -> begin
(cthen false)
end)))
in (

let comp = (FStar_List.fold_right (fun uu____6005 celse -> (match (uu____6005) with
| (g, eff_label, uu____6021, cthen) -> begin
(

let uu____6031 = (

let uu____6056 = (

let uu____6057 = (maybe_return eff_label cthen)
in (FStar_Syntax_Syntax.lcomp_comp uu____6057))
in (lift_and_destruct env uu____6056 celse))
in (match (uu____6031) with
| ((md, uu____6059, uu____6060), (uu____6061, uu____6062, wp_then), (uu____6064, uu____6065, wp_else)) -> begin
(

let uu____6085 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____6085 []))
end))
end)) lcases default_case)
in (match (lcases) with
| [] -> begin
comp
end
| (uu____6098)::[] -> begin
comp
end
| uu____6135 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____6152 = (destruct_comp comp1)
in (match (uu____6152) with
| (uu____6159, uu____6160, wp) -> begin
(

let wp1 = (

let uu____6165 = (

let uu____6166 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____6167 = (

let uu____6168 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____6169 = (

let uu____6172 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6172)::[])
in (uu____6168)::uu____6169))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6166 uu____6167)))
in (uu____6165 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 bind_cases_flags))
end))))
end)))))
end))))
in (FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags bind_cases))
end))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____6199 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____6199) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6208 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____6213 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____6208 uu____6213)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_prop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let is_prop = (fun t1 -> (

let uu____6245 = (

let uu____6246 = (FStar_Syntax_Util.unrefine t1)
in uu____6246.FStar_Syntax_Syntax.n)
in (match (uu____6245) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.prop_lid)
end
| uu____6250 -> begin
false
end)))
in (

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____6256 = (

let uu____6257 = (FStar_Syntax_Subst.compress t2)
in uu____6257.FStar_Syntax_Syntax.n)
in (match (uu____6256) with
| FStar_Syntax_Syntax.Tm_type (uu____6260) -> begin
true
end
| uu____6261 -> begin
false
end))))
in (

let uu____6262 = (

let uu____6263 = (FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ)
in uu____6263.FStar_Syntax_Syntax.n)
in (match (uu____6262) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && ((is_prop t) || (is_type1 t))) -> begin
(

let uu____6271 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2p_lid)
in (

let b2p1 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.b2p_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let lc1 = (

let uu____6282 = (

let uu____6283 = (

let uu____6284 = (

let uu____6287 = (

let uu____6288 = (is_prop t)
in (match (uu____6288) with
| true -> begin
FStar_Syntax_Util.kprop
end
| uu____6289 -> begin
FStar_Syntax_Util.ktype0
end))
in (FStar_Syntax_Syntax.mk_Total uu____6287))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6284))
in ((FStar_Pervasives_Native.None), (uu____6283)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____6282))
in (

let e1 = (

let uu____6297 = (

let uu____6298 = (

let uu____6299 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6299)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2p1 uu____6298))
in (uu____6297 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____6304 -> begin
((e), (lc))
end)))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____6333 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____6333) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____6356 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____6378 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____6378), (false)))
end
| uu____6383 -> begin
(

let uu____6384 = (FStar_TypeChecker_Rel.get_subtyping_predicate env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____6384), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____6395) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____6404 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Errors.raise_error uu____6404 e.FStar_Syntax_Syntax.pos))
end
| uu____6415 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___120_6418 = lc
in {FStar_Syntax_Syntax.eff_name = uu___120_6418.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___120_6418.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___120_6418.FStar_Syntax_Syntax.comp_thunk})), (FStar_TypeChecker_Rel.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____6423 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____6423) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___121_6431 = lc
in {FStar_Syntax_Syntax.eff_name = uu___121_6431.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___121_6431.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___121_6431.FStar_Syntax_Syntax.comp_thunk})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___122_6434 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___122_6434.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___122_6434.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___122_6434.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____6438 -> (

let uu____6439 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____6439) with
| true -> begin
(FStar_Syntax_Syntax.lcomp_comp lc)
end
| uu____6440 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in (

let uu____6442 = (

let uu____6443 = (FStar_Syntax_Subst.compress f1)
in uu____6443.FStar_Syntax_Syntax.n)
in (match (uu____6442) with
| FStar_Syntax_Syntax.Tm_abs (uu____6446, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6448; FStar_Syntax_Syntax.vars = uu____6449}, uu____6450) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___123_6472 = lc
in {FStar_Syntax_Syntax.eff_name = uu___123_6472.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___123_6472.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___123_6472.FStar_Syntax_Syntax.comp_thunk})
in (FStar_Syntax_Syntax.lcomp_comp lc1))
end
| uu____6473 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((

let uu____6476 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6476) with
| true -> begin
(

let uu____6477 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____6478 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____6479 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____6480 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____6477 uu____6478 uu____6479 uu____6480)))))
end
| uu____6481 -> begin
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

let uu____6493 = (

let uu____6494 = (

let uu____6495 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____6495)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____6494))
in (uu____6493 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____6498 -> begin
f1
end)
in (

let uu____6499 = (

let uu____6504 = (FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____6517 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____6518 = (FStar_Syntax_Util.lcomp_of_comp cret)
in (

let uu____6519 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____6504 uu____6517 e uu____6518 uu____6519)))))
in (match (uu____6499) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___124_6523 = x
in {FStar_Syntax_Syntax.ppname = uu___124_6523.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_6523.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____6525 = (FStar_Syntax_Util.lcomp_of_comp c)
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____6525 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((

let uu____6530 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6530) with
| true -> begin
(

let uu____6531 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____6531))
end
| uu____6532 -> begin
()
end));
c2;
))))
end)))))));
))
end)))
end)))
in (

let flags1 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___90_6541 -> (match (uu___90_6541) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____6544 -> begin
[]
end))))
in (

let lc1 = (

let uu____6546 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____6546 t flags1 strengthen))
in (

let g2 = (

let uu___125_6548 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___125_6548.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___125_6548.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___125_6548.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____6571 = (

let uu____6572 = (

let uu____6573 = (

let uu____6574 = (

let uu____6575 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____6575))
in (uu____6574)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____6573))
in (uu____6572 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____6571))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____6582 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____6582) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____6593 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____6600) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____6615) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____6644))::((ens, uu____6646))::uu____6647 -> begin
(

let uu____6676 = (

let uu____6679 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____6679))
in (

let uu____6680 = (

let uu____6681 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____6681))
in ((uu____6676), (uu____6680))))
end
| uu____6684 -> begin
(

let uu____6693 = (

let uu____6698 = (

let uu____6699 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____6699))
in ((FStar_Errors.Fatal_EffectConstructorNotFullyApplied), (uu____6698)))
in (FStar_Errors.raise_error uu____6693 comp.FStar_Syntax_Syntax.pos))
end)
end
| uu____6706 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____6715))::uu____6716 -> begin
(

let uu____6735 = (

let uu____6740 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6740))
in (match (uu____6735) with
| (us_r, uu____6772) -> begin
(

let uu____6773 = (

let uu____6778 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6778))
in (match (uu____6773) with
| (us_e, uu____6810) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____6813 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6813 us_r))
in (

let as_ens = (

let uu____6815 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6815 us_e))
in (

let req = (

let uu____6819 = (

let uu____6820 = (

let uu____6821 = (

let uu____6832 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6832)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____6821)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____6820))
in (uu____6819 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____6850 = (

let uu____6851 = (

let uu____6852 = (

let uu____6863 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6863)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____6852)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____6851))
in (uu____6850 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____6878 = (

let uu____6881 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____6881))
in (

let uu____6882 = (

let uu____6883 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____6883))
in ((uu____6878), (uu____6882)))))))))
end))
end))
end
| uu____6886 -> begin
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

let uu____6912 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6912) with
| true -> begin
(

let uu____6913 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6914 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6913 uu____6914)))
end
| uu____6915 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____6932 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6932) with
| true -> begin
(

let uu____6933 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6934 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6933 uu____6934)))
end
| uu____6935 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____6939 = (

let uu____6940 = (

let uu____6941 = (FStar_Syntax_Subst.compress t)
in uu____6941.FStar_Syntax_Syntax.n)
in (match (uu____6940) with
| FStar_Syntax_Syntax.Tm_app (uu____6944) -> begin
false
end
| uu____6959 -> begin
true
end))
in (match (uu____6939) with
| true -> begin
t
end
| uu____6960 -> begin
(

let uu____6961 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6961) with
| (head1, args) -> begin
(

let uu____6998 = (

let uu____6999 = (

let uu____7000 = (FStar_Syntax_Subst.compress head1)
in uu____7000.FStar_Syntax_Syntax.n)
in (match (uu____6999) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____7003 -> begin
false
end))
in (match (uu____6998) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____7025 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____7034 -> begin
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
| uu____7057 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____7062 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____7062) with
| (formals, uu____7076) -> begin
(

let n_implicits = (

let uu____7094 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____7170 -> (match (uu____7170) with
| (uu____7177, imp) -> begin
((Prims.op_Equality imp FStar_Pervasives_Native.None) || (Prims.op_Equality imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality))))
end))))
in (match (uu____7094) with
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

let uu____7308 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____7308) with
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

let uu____7332 = (

let uu____7337 = (

let uu____7338 = (FStar_Util.string_of_int n_expected)
in (

let uu____7345 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7346 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____7338 uu____7345 uu____7346))))
in ((FStar_Errors.Fatal_MissingImplicitArguments), (uu____7337)))
in (

let uu____7353 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____7332 uu____7353)))
end
| uu____7356 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___91_7374 -> (match (uu___91_7374) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7404 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7404) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_41), uu____7513) when (_0_41 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____7556, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____7589 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____7589) with
| (v1, uu____7629, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____7646 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____7646) with
| (args, bs3, subst3, g') -> begin
(

let uu____7739 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____7739)))
end)))
end)))
end
| (uu____7766, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____7812 = (

let uu____7839 = (inst_n_binders t)
in (aux [] uu____7839 bs1))
in (match (uu____7812) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____7910) -> begin
((e), (torig), (guard))
end
| (uu____7941, []) when (

let uu____7972 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____7972))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____7973 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____8005 -> begin
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
| uu____8020 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____8028 = (

let uu____8031 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____8031 (FStar_List.map (fun u -> (

let uu____8041 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____8041 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____8028 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____8058 = (FStar_Util.set_is_empty x)
in (match (uu____8058) with
| true -> begin
[]
end
| uu____8061 -> begin
(

let s = (

let uu____8065 = (

let uu____8068 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____8068))
in (FStar_All.pipe_right uu____8065 FStar_Util.set_elements))
in ((

let uu____8076 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8076) with
| true -> begin
(

let uu____8077 = (

let uu____8078 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____8078))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____8077))
end
| uu____8081 -> begin
()
end));
(

let r = (

let uu____8085 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____8085))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____8100 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8100) with
| true -> begin
(

let uu____8101 = (

let uu____8102 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____8102))
in (

let uu____8103 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____8104 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____8101 uu____8103 uu____8104))))
end
| uu____8105 -> begin
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

let uu____8126 = (FStar_Util.set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____8126 FStar_Util.set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____8158) -> begin
generalized_univ_names
end
| (uu____8165, []) -> begin
explicit_univ_names
end
| uu____8172 -> begin
(

let uu____8181 = (

let uu____8186 = (

let uu____8187 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____8187))
in ((FStar_Errors.Fatal_UnexpectedGeneralizedUniverse), (uu____8186)))
in (FStar_Errors.raise_error uu____8181 t.FStar_Syntax_Syntax.pos))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in ((

let uu____8201 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8201) with
| true -> begin
(

let uu____8202 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____8203 = (FStar_Syntax_Print.univ_names_to_string univnames1)
in (FStar_Util.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" uu____8202 uu____8203)))
end
| uu____8204 -> begin
()
end));
(

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____8209 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8209) with
| true -> begin
(

let uu____8210 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____8210))
end
| uu____8211 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____8216 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8216) with
| true -> begin
(

let uu____8217 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____8218 = (FStar_Syntax_Print.univ_names_to_string gen1)
in (FStar_Util.print2 "After generalization, t: %s and univs: %s\n" uu____8217 uu____8218)))
end
| uu____8219 -> begin
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

let uu____8288 = (

let uu____8289 = (FStar_Util.for_all (fun uu____8302 -> (match (uu____8302) with
| (uu____8311, uu____8312, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____8289))
in (match (uu____8288) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8352 -> begin
(

let norm1 = (fun c -> ((

let uu____8358 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8358) with
| true -> begin
(

let uu____8359 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____8359))
end
| uu____8360 -> begin
()
end));
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env c)
in ((

let uu____8363 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8363) with
| true -> begin
(

let uu____8364 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8364))
end
| uu____8365 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____8425 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____8425 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____8555 -> (match (uu____8555) with
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

let uu____8621 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8621) with
| true -> begin
(

let uu____8622 = (

let uu____8623 = (

let uu____8626 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____8626 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8623 (FStar_String.concat ", ")))
in (

let uu____8653 = (

let uu____8654 = (

let uu____8657 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____8657 (FStar_List.map (fun uu____8685 -> (match (uu____8685) with
| (u, t2) -> begin
(

let uu____8692 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____8693 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s : %s)" uu____8692 uu____8693)))
end)))))
in (FStar_All.pipe_right uu____8654 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8622 uu____8653)))
end
| uu____8696 -> begin
()
end));
(

let univs2 = (

let uu____8700 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uu____8723 -> (match (uu____8723) with
| (uu____8732, t2) -> begin
(

let uu____8734 = (FStar_Syntax_Free.univs t2)
in (FStar_Util.set_union univs2 uu____8734))
end)) univs1 uu____8700))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____8757 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8757) with
| true -> begin
(

let uu____8758 = (

let uu____8759 = (

let uu____8762 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____8762 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8759 (FStar_String.concat ", ")))
in (

let uu____8789 = (

let uu____8790 = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____8822 -> (match (uu____8822) with
| (u, t2) -> begin
(

let uu____8829 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____8830 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "(%s : %s)" uu____8829 uu____8830)))
end))))
in (FStar_All.pipe_right uu____8790 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8758 uu____8789)))
end
| uu____8833 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
))))))
end))
in (

let uu____8860 = (

let uu____8893 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____8893))
in (match (uu____8860) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____9011 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____9011) with
| true -> begin
()
end
| uu____9012 -> begin
(

let uu____9013 = lec_hd
in (match (uu____9013) with
| (lb1, uu____9021, uu____9022) -> begin
(

let uu____9023 = lec2
in (match (uu____9023) with
| (lb2, uu____9031, uu____9032) -> begin
(

let msg = (

let uu____9034 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____9035 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____9034 uu____9035)))
in (

let uu____9036 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleSetOfUniverse), (msg)) uu____9036)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun uu____9147 -> (match (uu____9147) with
| (u, uu____9155) -> begin
(FStar_All.pipe_right u21 (FStar_Util.for_some (fun uu____9177 -> (match (uu____9177) with
| (u', uu____9185) -> begin
(FStar_Syntax_Unionfind.equiv u u')
end))))
end)))))
in (

let uu____9190 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____9190) with
| true -> begin
()
end
| uu____9191 -> begin
(

let uu____9192 = lec_hd
in (match (uu____9192) with
| (lb1, uu____9200, uu____9201) -> begin
(

let uu____9202 = lec2
in (match (uu____9202) with
| (lb2, uu____9210, uu____9211) -> begin
(

let msg = (

let uu____9213 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____9214 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____9213 uu____9214)))
in (

let uu____9215 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleNumberOfTypes), (msg)) uu____9215)))
end))
end))
end))))
in (

let lecs1 = (

let uu____9225 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____9284 = (univs_and_uvars_of_lec this_lec)
in (match (uu____9284) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____9225 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail1 = (fun k -> (

let uu____9437 = lec_hd
in (match (uu____9437) with
| (lbname, e, c) -> begin
(

let uu____9447 = (

let uu____9452 = (

let uu____9453 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9454 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____9455 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____9453 uu____9454 uu____9455))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____9452)))
in (

let uu____9456 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____9447 uu____9456)))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun uu____9486 -> (match (uu____9486) with
| (u, k) -> begin
(

let uu____9499 = (FStar_Syntax_Unionfind.find u)
in (match (uu____9499) with
| FStar_Pervasives_Native.Some (uu____9508) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____9515 -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env k)
in (

let uu____9519 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____9519) with
| (bs, kres) -> begin
((

let uu____9557 = (

let uu____9558 = (

let uu____9561 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____9561))
in uu____9558.FStar_Syntax_Syntax.n)
in (match (uu____9557) with
| FStar_Syntax_Syntax.Tm_type (uu____9562) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____9566 = (

let uu____9567 = (FStar_Util.set_is_empty free)
in (not (uu____9567)))
in (match (uu____9566) with
| true -> begin
(fail1 kres)
end
| uu____9568 -> begin
()
end)))
end
| uu____9569 -> begin
(fail1 kres)
end));
(

let a = (

let uu____9571 = (

let uu____9574 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____9574))
in (FStar_Syntax_Syntax.new_bv uu____9571 kres))
in (

let t = (

let uu____9578 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____9578 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
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

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____9697 -> (match (uu____9697) with
| (lbname, e, c) -> begin
(

let uu____9743 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____9812 -> begin
(

let uu____9827 = ((e), (c))
in (match (uu____9827) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____9864 -> (match (uu____9864) with
| (x, uu____9872) -> begin
(

let uu____9877 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____9877))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____9887 = (

let uu____9888 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____9888))
in (match (uu____9887) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____9891 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____9892 -> begin
e1
end)
in (

let t = (

let uu____9896 = (

let uu____9897 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____9897.FStar_Syntax_Syntax.n)
in (match (uu____9896) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____9920 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____9920) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____9935 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____9937 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____9937), (gen_tvars))))))))
end))
end)
in (match (uu____9743) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____10083 = (Obj.magic (()))
in ());
(

let uu____10097 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____10097) with
| true -> begin
(

let uu____10098 = (

let uu____10099 = (FStar_List.map (fun uu____10112 -> (match (uu____10112) with
| (lb, uu____10120, uu____10121) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____10099 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____10098))
end
| uu____10124 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____10142 -> (match (uu____10142) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____10171 = (gen env is_rec lecs)
in (match (uu____10171) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____10270 -> (match (uu____10270) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____10332 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____10332) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____10376 -> (match (uu____10376) with
| (l, us, e, c, gvs) -> begin
(

let uu____10410 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____10411 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____10412 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____10413 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____10414 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____10410 uu____10411 uu____10412 uu____10413 uu____10414))))))
end))))
end
| uu____10415 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____10455 -> (match (uu____10455) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____10499 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____10499), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check1 = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____10541 -> begin
(

let uu____10542 = (FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21)
in (match (uu____10542) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____10548 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____10548))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____10555 = (

let uu____10556 = (FStar_Syntax_Subst.compress e1)
in uu____10556.FStar_Syntax_Syntax.n)
in (match (uu____10555) with
| FStar_Syntax_Syntax.Tm_name (uu____10559) -> begin
true
end
| uu____10560 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___126_10576 = x
in {FStar_Syntax_Syntax.ppname = uu___126_10576.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___126_10576.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____10577 -> begin
e2
end)))
in (

let env2 = (

let uu___127_10579 = env1
in (

let uu____10580 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___127_10579.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___127_10579.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___127_10579.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___127_10579.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___127_10579.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___127_10579.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___127_10579.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___127_10579.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___127_10579.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___127_10579.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___127_10579.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___127_10579.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___127_10579.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___127_10579.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___127_10579.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____10580; FStar_TypeChecker_Env.is_iface = uu___127_10579.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___127_10579.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___127_10579.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___127_10579.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___127_10579.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___127_10579.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___127_10579.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___127_10579.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___127_10579.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___127_10579.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___127_10579.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___127_10579.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___127_10579.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___127_10579.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___127_10579.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___127_10579.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___127_10579.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___127_10579.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___127_10579.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___127_10579.FStar_TypeChecker_Env.dep_graph}))
in (

let uu____10581 = (check1 env2 t1 t2)
in (match (uu____10581) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10588 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____10593 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____10588 uu____10593)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____10600 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____10600) with
| true -> begin
(

let uu____10601 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____10601))
end
| uu____10602 -> begin
()
end));
(

let uu____10603 = (decorate e t2)
in ((uu____10603), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____10631 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____10631) with
| true -> begin
(

let uu____10636 = (discharge g1)
in (

let uu____10637 = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((uu____10636), (uu____10637))))
end
| uu____10638 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]
in (

let c1 = (

let uu____10644 = (

let uu____10645 = (

let uu____10646 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____10646 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____10645 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____10644 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____10648 = (destruct_comp c1)
in (match (uu____10648) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____10665 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____10666 = (

let uu____10667 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____10668 = (

let uu____10669 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____10670 = (

let uu____10673 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____10673)::[])
in (uu____10669)::uu____10670))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10667 uu____10668)))
in (uu____10666 FStar_Pervasives_Native.None uu____10665)))
in ((

let uu____10677 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10677) with
| true -> begin
(

let uu____10678 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____10678))
end
| uu____10679 -> begin
()
end));
(

let g2 = (

let uu____10681 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____10681))
in (

let uu____10682 = (discharge g2)
in (

let uu____10683 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____10682), (uu____10683)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___92_10707 -> (match (uu___92_10707) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____10715))::[] -> begin
(f fst1)
end
| uu____10732 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____10737 = (FStar_Syntax_Util.b2p e)
in (FStar_All.pipe_right uu____10737 (fun _0_44 -> FStar_TypeChecker_Common.NonTrivial (_0_44)))))
in (

let op_or_e = (fun e -> (

let uu____10746 = (

let uu____10749 = (FStar_Syntax_Util.b2p e)
in (FStar_Syntax_Util.mk_neg uu____10749))
in (FStar_All.pipe_right uu____10746 (fun _0_45 -> FStar_TypeChecker_Common.NonTrivial (_0_45)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_46 -> FStar_TypeChecker_Common.NonTrivial (_0_46))))
in (

let op_or_t = (fun t -> (

let uu____10760 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____10760 (fun _0_47 -> FStar_TypeChecker_Common.NonTrivial (_0_47)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_48 -> FStar_TypeChecker_Common.NonTrivial (_0_48))))
in (

let short_op_ite = (fun uu___93_10774 -> (match (uu___93_10774) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____10782))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____10801))::[] -> begin
(

let uu____10830 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____10830 (fun _0_49 -> FStar_TypeChecker_Common.NonTrivial (_0_49))))
end
| uu____10835 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____10845 = (

let uu____10852 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____10852)))
in (

let uu____10857 = (

let uu____10866 = (

let uu____10873 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____10873)))
in (

let uu____10878 = (

let uu____10887 = (

let uu____10894 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____10894)))
in (

let uu____10899 = (

let uu____10908 = (

let uu____10915 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____10915)))
in (

let uu____10920 = (

let uu____10929 = (

let uu____10936 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____10936)))
in (uu____10929)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____10908)::uu____10920))
in (uu____10887)::uu____10899))
in (uu____10866)::uu____10878))
in (uu____10845)::uu____10857))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10987 = (FStar_Util.find_map table (fun uu____11000 -> (match (uu____11000) with
| (x, mk1) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
(

let uu____11017 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____11017))
end
| uu____11018 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (uu____10987) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____11020 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____11024 = (

let uu____11025 = (FStar_Syntax_Util.un_uinst l)
in uu____11025.FStar_Syntax_Syntax.n)
in (match (uu____11024) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____11029 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____11053))::uu____11054 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____11065 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____11072, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11073))))::uu____11074 -> begin
bs
end
| uu____11091 -> begin
(

let uu____11092 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____11092) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____11096 = (

let uu____11097 = (FStar_Syntax_Subst.compress t)
in uu____11097.FStar_Syntax_Syntax.n)
in (match (uu____11096) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____11101) -> begin
(

let uu____11118 = (FStar_Util.prefix_until (fun uu___94_11158 -> (match (uu___94_11158) with
| (uu____11165, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11166))) -> begin
false
end
| uu____11169 -> begin
true
end)) bs')
in (match (uu____11118) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____11204, uu____11205) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____11277, uu____11278) -> begin
(

let uu____11351 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____11369 -> (match (uu____11369) with
| (x, uu____11377) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____11351) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____11424 -> (match (uu____11424) with
| (x, i) -> begin
(

let uu____11443 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____11443), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____11452 -> begin
bs
end))
end))
end
| uu____11453 -> begin
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
| uu____11471 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____11485 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____11485) with
| true -> begin
e
end
| uu____11486 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____11508 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____11508) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(

let uu____11510 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) uu____11510));
)
end
| uu____11511 -> begin
()
end));
(

let fv = (

let uu____11513 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____11513 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (((FStar_Syntax_Util.mk_letbinding lbname [] FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def [] FStar_Range.dummyRange))::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____11523 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___128_11529 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___128_11529.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___128_11529.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___128_11529.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___128_11529.FStar_Syntax_Syntax.sigattrs})), (uu____11523)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___95_11539 -> (match (uu___95_11539) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11540 -> begin
false
end))
in (

let reducibility = (fun uu___96_11544 -> (match (uu___96_11544) with
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
| uu____11545 -> begin
false
end))
in (

let assumption = (fun uu___97_11549 -> (match (uu___97_11549) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____11550 -> begin
false
end))
in (

let reification = (fun uu___98_11554 -> (match (uu___98_11554) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____11555) -> begin
true
end
| uu____11556 -> begin
false
end))
in (

let inferred = (fun uu___99_11560 -> (match (uu___99_11560) with
| FStar_Syntax_Syntax.Discriminator (uu____11561) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____11562) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____11567) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____11576) -> begin
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
| uu____11585 -> begin
false
end))
in (

let has_eq = (fun uu___100_11589 -> (match (uu___100_11589) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____11590 -> begin
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
| FStar_Syntax_Syntax.Reflectable (uu____11650) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11655 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____11659 = (

let uu____11660 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___101_11664 -> (match (uu___101_11664) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____11665 -> begin
false
end))))
in (FStar_All.pipe_right uu____11660 Prims.op_Negation))
in (match (uu____11659) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____11678 = (

let uu____11683 = (

let uu____11684 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____11684 msg))
in ((FStar_Errors.Fatal_QulifierListNotPermitted), (uu____11683)))
in (FStar_Errors.raise_error uu____11678 r)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____11692 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____11694 -> begin
()
end);
(

let uu____11696 = (

let uu____11697 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____11697)))
in (match (uu____11696) with
| true -> begin
(err "ill-formed combination")
end
| uu____11700 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____11702), uu____11703) -> begin
((

let uu____11719 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____11719) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____11722 -> begin
()
end));
(

let uu____11723 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____11723) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____11728 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____11729) -> begin
(

let uu____11738 = (

let uu____11739 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____11739)))
in (match (uu____11738) with
| true -> begin
(err'1 ())
end
| uu____11744 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____11745) -> begin
(

let uu____11752 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____11752) with
| true -> begin
(err'1 ())
end
| uu____11755 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____11756) -> begin
(

let uu____11763 = (

let uu____11764 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____11764)))
in (match (uu____11763) with
| true -> begin
(err'1 ())
end
| uu____11769 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____11770) -> begin
(

let uu____11771 = (

let uu____11772 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11772)))
in (match (uu____11771) with
| true -> begin
(err'1 ())
end
| uu____11777 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____11778) -> begin
(

let uu____11779 = (

let uu____11780 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11780)))
in (match (uu____11779) with
| true -> begin
(err'1 ())
end
| uu____11785 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____11786) -> begin
(

let uu____11799 = (

let uu____11800 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____11800)))
in (match (uu____11799) with
| true -> begin
(err'1 ())
end
| uu____11805 -> begin
()
end))
end
| uu____11806 -> begin
()
end);
))))))
end
| uu____11807 -> begin
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

let uu____11869 = (

let uu____11872 = (

let uu____11873 = (

let uu____11880 = (

let uu____11881 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____11881))
in ((uu____11880), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____11873))
in (FStar_Syntax_Syntax.mk uu____11872))
in (uu____11869 FStar_Pervasives_Native.None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____11922 -> (match (uu____11922) with
| (x, imp) -> begin
(

let uu____11933 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____11933), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args FStar_Pervasives_Native.None p)))
in (

let unrefined_arg_binder = (

let uu____11935 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____11935))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____11937 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____11944 = (

let uu____11945 = (

let uu____11946 = (

let uu____11947 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____11948 = (

let uu____11949 = (

let uu____11950 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11950))
in (uu____11949)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____11947 uu____11948)))
in (uu____11946 FStar_Pervasives_Native.None p))
in (FStar_Syntax_Util.b2p uu____11945))
in (FStar_Syntax_Util.refine x uu____11944)))
in (

let uu____11953 = (

let uu___129_11954 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___129_11954.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_11954.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____11953)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____11969 = (FStar_List.map (fun uu____11991 -> (match (uu____11991) with
| (x, uu____12003) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____11969 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____12052 -> (match (uu____12052) with
| (x, uu____12064) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____12072 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((

let uu____12078 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____12078)) || (

let uu____12080 = (

let uu____12081 = (FStar_TypeChecker_Env.current_module env)
in uu____12081.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____12080)))
in (

let quals = (

let uu____12085 = (FStar_List.filter (fun uu___102_12089 -> (match (uu___102_12089) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____12090 -> begin
false
end)) iquals)
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____12093 -> begin
[]
end)) uu____12085))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____12111 = (

let uu____12112 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____12112))
in (FStar_Syntax_Syntax.mk_Total uu____12111))
in (

let uu____12113 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____12113)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid discriminator_name); FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((

let uu____12116 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12116) with
| true -> begin
(

let uu____12117 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____12117))
end
| uu____12118 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____12121 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____12127 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____12170 -> (match (uu____12170) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____12194 = (

let uu____12197 = (

let uu____12198 = (

let uu____12205 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____12205), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____12198))
in (pos uu____12197))
in ((uu____12194), (b)))
end
| uu____12208 -> begin
(

let uu____12209 = (

let uu____12212 = (

let uu____12213 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____12213))
in (pos uu____12212))
in ((uu____12209), (b)))
end))
end))))
in (

let pat_true = (

let uu____12231 = (

let uu____12234 = (

let uu____12235 = (

let uu____12248 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____12248), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____12235))
in (pos uu____12234))
in ((uu____12231), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_true_bool)))
in (

let pat_false = (

let uu____12282 = (

let uu____12285 = (

let uu____12286 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____12286))
in (pos uu____12285))
in ((uu____12282), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst unrefined_arg_binder))
in (

let uu____12298 = (

let uu____12301 = (

let uu____12302 = (

let uu____12325 = (

let uu____12328 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____12329 = (

let uu____12332 = (FStar_Syntax_Util.branch pat_false)
in (uu____12332)::[])
in (uu____12328)::uu____12329))
in ((arg_exp), (uu____12325)))
in FStar_Syntax_Syntax.Tm_match (uu____12302))
in (FStar_Syntax_Syntax.mk uu____12301))
in (uu____12298 FStar_Pervasives_Native.None p))))))
end)
in (

let dd = (

let uu____12339 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____12339) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____12342 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____12345 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____12347 = (

let uu____12352 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____12352))
in (

let uu____12353 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in (FStar_Syntax_Util.mk_letbinding uu____12347 uvs lbtyp FStar_Parser_Const.effect_Tot_lid uu____12353 [] FStar_Range.dummyRange)))
in (

let impl = (

let uu____12359 = (

let uu____12360 = (

let uu____12367 = (

let uu____12370 = (

let uu____12371 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____12371 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____12370)::[])
in ((((false), ((lb)::[]))), (uu____12367)))
in FStar_Syntax_Syntax.Sig_let (uu____12360))
in {FStar_Syntax_Syntax.sigel = uu____12359; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____12389 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12389) with
| true -> begin
(

let uu____12390 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____12390))
end
| uu____12391 -> begin
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

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____12432 -> (match (uu____12432) with
| (a, uu____12438) -> begin
(

let uu____12439 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____12439) with
| (field_name, uu____12445) -> begin
(

let field_proj_tm = (

let uu____12447 = (

let uu____12448 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____12448))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____12447 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) FStar_Pervasives_Native.None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____12465 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____12497 -> (match (uu____12497) with
| (x, uu____12505) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____12507 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____12507) with
| (field_name, uu____12515) -> begin
(

let t = (

let uu____12517 = (

let uu____12518 = (

let uu____12521 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____12521))
in (FStar_Syntax_Util.arrow binders uu____12518))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____12517))
in (

let only_decl = ((

let uu____12525 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____12525)) || (

let uu____12527 = (

let uu____12528 = (FStar_TypeChecker_Env.current_module env)
in uu____12528.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____12527)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____12542 = (FStar_List.filter (fun uu___103_12546 -> (match (uu___103_12546) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____12547 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____12542)
end
| uu____12548 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___104_12560 -> (match (uu___104_12560) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____12561 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let attrs = (match (only_decl) with
| true -> begin
[]
end
| uu____12573 -> begin
(FStar_Syntax_Util.attr_substitute)::[]
end)
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs}
in ((

let uu____12580 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12580) with
| true -> begin
(

let uu____12581 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____12581))
end
| uu____12582 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____12585 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____12629 -> (match (uu____12629) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((Prims.op_Equality (i + ntps) j)) with
| true -> begin
(

let uu____12653 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____12653), (b)))
end
| uu____12658 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____12669 = (

let uu____12672 = (

let uu____12673 = (

let uu____12680 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____12680), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____12673))
in (pos uu____12672))
in ((uu____12669), (b)))
end
| uu____12683 -> begin
(

let uu____12684 = (

let uu____12687 = (

let uu____12688 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____12688))
in (pos uu____12687))
in ((uu____12684), (b)))
end)
end))
end))))
in (

let pat = (

let uu____12704 = (

let uu____12707 = (

let uu____12708 = (

let uu____12721 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____12721), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____12708))
in (pos uu____12707))
in (

let uu____12730 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____12704), (FStar_Pervasives_Native.None), (uu____12730))))
in (

let body = (

let uu____12742 = (

let uu____12745 = (

let uu____12746 = (

let uu____12769 = (

let uu____12772 = (FStar_Syntax_Util.branch pat)
in (uu____12772)::[])
in ((arg_exp), (uu____12769)))
in FStar_Syntax_Syntax.Tm_match (uu____12746))
in (FStar_Syntax_Syntax.mk uu____12745))
in (uu____12742 FStar_Pervasives_Native.None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let dd = (

let uu____12780 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____12780) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____12783 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____12785 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____12787 = (

let uu____12792 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____12792))
in (

let uu____12793 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____12787; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____12793; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange}))
in (

let impl = (

let uu____12799 = (

let uu____12800 = (

let uu____12807 = (

let uu____12810 = (

let uu____12811 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____12811 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____12810)::[])
in ((((false), ((lb)::[]))), (uu____12807)))
in FStar_Syntax_Syntax.Sig_let (uu____12800))
in {FStar_Syntax_Syntax.sigel = uu____12799; FStar_Syntax_Syntax.sigrng = p1; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____12829 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____12829) with
| true -> begin
(

let uu____12830 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____12830))
end
| uu____12831 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____12834 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
))))))))
end)))
end))))
in (FStar_All.pipe_right uu____12465 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, uu____12870) when (not ((FStar_Ident.lid_equals constr_lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____12875 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____12875) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____12897 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____12897) with
| (formals, uu____12913) -> begin
(

let uu____12930 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____12962 = (

let uu____12963 = (

let uu____12964 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____12964))
in (FStar_Ident.lid_equals typ_lid uu____12963))
in (match (uu____12962) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____12983, uvs', tps, typ0, uu____12987, constrs) -> begin
FStar_Pervasives_Native.Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____13012 -> begin
(failwith "Impossible")
end)
end
| uu____13021 -> begin
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
| uu____13071 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedDataConstructor), ("Unexpected data constructor")) se.FStar_Syntax_Syntax.sigrng)
end)
end))
in (match (uu____12930) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____13085 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____13085) with
| (indices, uu____13101) -> begin
(

let refine_domain = (

let uu____13119 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___105_13124 -> (match (uu___105_13124) with
| FStar_Syntax_Syntax.RecordConstructor (uu____13125) -> begin
true
end
| uu____13134 -> begin
false
end))))
in (match (uu____13119) with
| true -> begin
false
end
| uu____13135 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___106_13142 -> (match (uu___106_13142) with
| FStar_Syntax_Syntax.RecordConstructor (uu____13145, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____13157 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____13158 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____13158) with
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
| uu____13167 -> begin
iquals
end)
in (

let fields = (

let uu____13169 = (FStar_Util.first_N n_typars formals)
in (match (uu____13169) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____13234 uu____13235 -> (match (((uu____13234), (uu____13235))) with
| ((x, uu____13253), (x', uu____13255)) -> begin
(

let uu____13264 = (

let uu____13271 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____13271)))
in FStar_Syntax_Syntax.NT (uu____13264))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____13272 -> begin
[]
end))


let haseq_suffix : Prims.string = "__uu___haseq"


let is_haseq_lid : FStar_Ident.lid  ->  Prims.bool = (fun lid -> (

let str = lid.FStar_Ident.str
in (

let len = (FStar_String.length str)
in (

let haseq_suffix_len = (FStar_String.length haseq_suffix)
in ((len > haseq_suffix_len) && (

let uu____13290 = (

let uu____13291 = (FStar_String.substring str (len - haseq_suffix_len) haseq_suffix_len)
in (FStar_String.compare uu____13291 haseq_suffix))
in (Prims.op_Equality uu____13290 (Prims.parse_int "0"))))))))


let get_haseq_axiom_lid : FStar_Ident.lid  ->  FStar_Ident.lid = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText haseq_suffix)))::[]))))


let get_optimized_haseq_axiom : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_names  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun en ty usubst us -> (

let uu____13345 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____13359, bs, t, uu____13362, uu____13363) -> begin
((lid), (bs), (t))
end
| uu____13372 -> begin
(failwith "Impossible!")
end)
in (match (uu____13345) with
| (lid, bs, t) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____13394 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____13394 t))
in (

let uu____13401 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____13401) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____13425 = (

let uu____13426 = (FStar_Syntax_Subst.compress t2)
in uu____13426.FStar_Syntax_Syntax.n)
in (match (uu____13425) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____13436) -> begin
ibs
end
| uu____13453 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____13460 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____13461 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____13460 uu____13461)))
in (

let ind1 = (

let uu____13467 = (

let uu____13468 = (FStar_List.map (fun uu____13481 -> (match (uu____13481) with
| (bv, aq) -> begin
(

let uu____13492 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____13492), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____13468))
in (uu____13467 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____13498 = (

let uu____13499 = (FStar_List.map (fun uu____13512 -> (match (uu____13512) with
| (bv, aq) -> begin
(

let uu____13523 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____13523), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____13499))
in (uu____13498 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____13529 = (

let uu____13530 = (

let uu____13531 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____13531)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____13530))
in (uu____13529 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____13552 = (

let uu____13553 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____13553))
in (FStar_TypeChecker_Rel.subtype_nosmt en (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort uu____13552))) bs2)
in (

let haseq_bs = (FStar_List.fold_left (fun t3 b -> (

let uu____13564 = (

let uu____13565 = (

let uu____13566 = (

let uu____13567 = (

let uu____13568 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b))
in (FStar_Syntax_Syntax.as_arg uu____13568))
in (uu____13567)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____13566))
in (uu____13565 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t3 uu____13564))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml1 = (

let uu___130_13575 = fml
in (

let uu____13576 = (

let uu____13577 = (

let uu____13584 = (

let uu____13585 = (

let uu____13596 = (

let uu____13599 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____13599)::[])
in (uu____13596)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____13585))
in ((fml), (uu____13584)))
in FStar_Syntax_Syntax.Tm_meta (uu____13577))
in {FStar_Syntax_Syntax.n = uu____13576; FStar_Syntax_Syntax.pos = uu___130_13575.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___130_13575.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____13612 = (

let uu____13613 = (

let uu____13614 = (

let uu____13615 = (

let uu____13616 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____13616 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____13615))
in (uu____13614)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____13613))
in (uu____13612 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____13641 = (

let uu____13642 = (

let uu____13643 = (

let uu____13644 = (

let uu____13645 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____13645 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____13644))
in (uu____13643)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____13642))
in (uu____13641 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
in (

let axiom_lid = (get_haseq_axiom_lid lid)
in ((axiom_lid), (fml3), (bs2), (ibs1), (haseq_bs)))))))))))))))
end))))
end)))




