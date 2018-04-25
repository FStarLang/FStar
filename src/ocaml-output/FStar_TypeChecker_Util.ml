
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  unit = (fun env errs -> (

let uu____21 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____22 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.log_issue uu____21 uu____22))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____32 = (

let uu____33 = (FStar_Syntax_Subst.compress t)
in uu____33.FStar_Syntax_Syntax.n)
in (match (uu____32) with
| FStar_Syntax_Syntax.Tm_type (uu____36) -> begin
true
end
| uu____37 -> begin
false
end)))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env -> (

let uu____49 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____49 (FStar_List.filter (fun uu____63 -> (match (uu____63) with
| (x, uu____69) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = (

let uu____85 = ((FStar_Options.full_context_dependency ()) || (

let uu____87 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____87)))
in (match (uu____85) with
| true -> begin
(FStar_TypeChecker_Env.all_binders env)
end
| uu____88 -> begin
(t_binders env)
end))
in (

let uu____89 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar uu____89 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (

let uu____100 = (new_uvar_aux env k)
in (FStar_Pervasives_Native.fst uu____100)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___80_112 -> (match (uu___80_112) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, uu____114); FStar_Syntax_Syntax.pos = uu____115; FStar_Syntax_Syntax.vars = uu____116} -> begin
uv
end
| uu____143 -> begin
(failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (

let uu____176 = (FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid)
in (match (uu____176) with
| FStar_Pervasives_Native.Some ((uu____199)::((tm, uu____201))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| uu____253 -> begin
(

let uu____264 = (new_uvar_aux env k)
in (match (uu____264) with
| (t, u) -> begin
(

let g = (

let uu___99_284 = FStar_TypeChecker_Rel.trivial_guard
in (

let uu____285 = (

let uu____300 = (

let uu____313 = (as_uvar u)
in ((reason), (env), (uu____313), (t), (k), (r)))
in (uu____300)::[])
in {FStar_TypeChecker_Env.guard_f = uu___99_284.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___99_284.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___99_284.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____285}))
in (

let uu____338 = (

let uu____345 = (

let uu____350 = (as_uvar u)
in ((uu____350), (r)))
in (uu____345)::[])
in ((t), (uu____338), (g))))
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____382 = (

let uu____383 = (FStar_Util.set_is_empty uvs)
in (not (uu____383)))
in (match (uu____382) with
| true -> begin
(

let us = (

let uu____389 = (

let uu____392 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun uu____410 -> (match (uu____410) with
| (x, uu____416) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) uu____392))
in (FStar_All.pipe_right uu____389 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____423 = (

let uu____428 = (

let uu____429 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____429))
in ((FStar_Errors.Error_UncontrainedUnificationVar), (uu____428)))
in (FStar_Errors.log_issue r uu____423));
(FStar_Options.pop ());
))
end
| uu____430 -> begin
()
end))))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____446 -> (match (uu____446) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____456; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____458; FStar_Syntax_Syntax.lbpos = uu____459} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____492 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 e)
in (match (uu____492) with
| (univ_vars2, e1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars2)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let mk_binder1 = (fun scope a -> (

let uu____524 = (

let uu____525 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in uu____525.FStar_Syntax_Syntax.n)
in (match (uu____524) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____532 = (FStar_Syntax_Util.type_u ())
in (match (uu____532) with
| (k, uu____542) -> begin
(

let t2 = (

let uu____544 = (FStar_TypeChecker_Rel.new_uvar e1.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right uu____544 FStar_Pervasives_Native.fst))
in (((

let uu___100_554 = a
in {FStar_Syntax_Syntax.ppname = uu___100_554.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___100_554.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (false)))
end))
end
| uu____555 -> begin
((a), (true))
end)))
in (

let rec aux = (fun must_check_ty vars e2 -> (

let e3 = (FStar_Syntax_Subst.compress e2)
in (match (e3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e4, uu____598) -> begin
(aux must_check_ty vars e4)
end
| FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____605) -> begin
(((FStar_Pervasives_Native.fst t2)), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____668) -> begin
(

let uu____689 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____749 uu____750 -> (match (((uu____749), (uu____750))) with
| ((scope, bs1, must_check_ty1), (a, imp)) -> begin
(

let uu____828 = (match (must_check_ty1) with
| true -> begin
((a), (true))
end
| uu____837 -> begin
(mk_binder1 scope a)
end)
in (match (uu____828) with
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
in (match (uu____689) with
| (scope, bs1, must_check_ty1) -> begin
(

let uu____940 = (aux must_check_ty1 scope body)
in (match (uu____940) with
| (res, must_check_ty2) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____969 = (FStar_Options.ml_ish ())
in (match (uu____969) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____970 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Util.arrow bs1 c)
in ((

let uu____976 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____976) with
| true -> begin
(

let uu____977 = (FStar_Range.string_of_range r)
in (

let uu____978 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____979 = (FStar_Util.string_of_bool must_check_ty2)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" uu____977 uu____978 uu____979))))
end
| uu____980 -> begin
()
end));
((FStar_Util.Inl (t2)), (must_check_ty2));
)))
end))
end))
end
| uu____989 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end
| uu____1002 -> begin
(

let uu____1003 = (

let uu____1008 = (

let uu____1009 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____1009 FStar_Pervasives_Native.fst))
in FStar_Util.Inl (uu____1008))
in ((uu____1003), (false)))
end)
end)))
in (

let uu____1022 = (

let uu____1031 = (t_binders env1)
in (aux false uu____1031 e1))
in (match (uu____1022) with
| (t2, b) -> begin
(

let t3 = (match (t2) with
| FStar_Util.Inr (c) -> begin
(

let uu____1056 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____1056) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1059 -> begin
(

let uu____1060 = (

let uu____1065 = (

let uu____1066 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____1066))
in ((FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec), (uu____1065)))
in (FStar_Errors.raise_error uu____1060 rng))
end))
end
| FStar_Util.Inl (t3) -> begin
t3
end)
in ((univ_vars2), (t3), (b)))
end))))))
end))
end
| uu____1072 -> begin
(

let uu____1073 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____1073) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let pat_as_exp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p tc_annot -> (

let check_bv = (fun env1 x -> (

let uu____1165 = (

let uu____1170 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in (match (uu____1170) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____1175; FStar_Syntax_Syntax.vars = uu____1176} -> begin
(

let uu____1179 = (FStar_Syntax_Util.type_u ())
in (match (uu____1179) with
| (t, uu____1189) -> begin
(

let uu____1190 = (new_uvar env1 t)
in ((uu____1190), (FStar_TypeChecker_Rel.trivial_guard)))
end))
end
| t -> begin
(tc_annot env1 t)
end))
in (match (uu____1165) with
| (t_x, guard) -> begin
(((

let uu___101_1199 = x
in {FStar_Syntax_Syntax.ppname = uu___101_1199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___101_1199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (guard))
end)))
in (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = (match (c) with
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(FStar_ToSyntax_ToSyntax.desugar_machine_integer env1.FStar_TypeChecker_Env.dsenv repr sw p1.FStar_Syntax_Syntax.p)
end
| uu____1274 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
end)
in (([]), ([]), ([]), (env1), (e), (FStar_TypeChecker_Rel.trivial_guard), (p1)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____1282) -> begin
(

let uu____1287 = (FStar_Syntax_Util.type_u ())
in (match (uu____1287) with
| (k, uu____1313) -> begin
(

let t = (new_uvar env1 k)
in (

let x1 = (

let uu___102_1316 = x
in {FStar_Syntax_Syntax.ppname = uu___102_1316.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_1316.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____1317 = (

let uu____1322 = (FStar_TypeChecker_Env.all_binders env1)
in (FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p uu____1322 t))
in (match (uu____1317) with
| (e, u) -> begin
(

let p2 = (

let uu___103_1348 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.p = uu___103_1348.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env1), (e), (FStar_TypeChecker_Rel.trivial_guard), (p2)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____1358 = (check_bv env1 x)
in (match (uu____1358) with
| (x1, g) -> begin
(

let env2 = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env1 x1)
end
| uu____1386 -> begin
env1
end)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (g), (p1))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____1399 = (check_bv env1 x)
in (match (uu____1399) with
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

let uu____1456 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1592 uu____1593 -> (match (((uu____1592), (uu____1593))) with
| ((b, a, w, env2, args, guard, pats1), (p2, imp)) -> begin
(

let uu____1791 = (pat_as_arg_with_env allow_wc_dependence env2 p2)
in (match (uu____1791) with
| (b', a', w', env3, te, guard', pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1866 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (

let uu____1867 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), (uu____1867), ((((pat), (imp)))::pats1))))
end))
end)) (([]), ([]), ([]), (env1), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([]))))
in (match (uu____1456) with
| (b, a, w, env2, args, guard, pats1) -> begin
(

let e = (

let uu____1998 = (

let uu____2003 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____2004 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____2003 uu____2004)))
in (uu____1998 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in (

let uu____2011 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____2022 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____2033 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____2011), (uu____2022), (uu____2033), (env2), (e), (guard), ((

let uu___104_2055 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___104_2055.FStar_Syntax_Syntax.p})))))))
end))
end))
in (

let rec elaborate_pat = (fun env1 p1 -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) r)
end
| uu____2103 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) r)
end))
in (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____2149 -> (match (uu____2149) with
| (p2, imp) -> begin
(

let uu____2168 = (elaborate_pat env1 p2)
in ((uu____2168), (imp)))
end)) pats)
in (

let uu____2173 = (FStar_TypeChecker_Env.lookup_datacon env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2173) with
| (uu____2180, t) -> begin
(

let uu____2182 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2182) with
| (f, uu____2198) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____2324)::uu____2325) -> begin
(

let uu____2368 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_TooManyPatternArguments), ("Too many pattern arguments")) uu____2368))
end
| ((uu____2377)::uu____2378, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____2456 -> (match (uu____2456) with
| (t1, imp) -> begin
(match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____2483 = (

let uu____2486 = (FStar_Syntax_Syntax.range_of_bv t1)
in FStar_Pervasives_Native.Some (uu____2486))
in (FStar_Syntax_Syntax.new_bv uu____2483 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2488 = (maybe_dot inaccessible a r)
in ((uu____2488), (true)))))
end
| uu____2493 -> begin
(

let uu____2496 = (

let uu____2501 = (

let uu____2502 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____2502))
in ((FStar_Errors.Fatal_InsufficientPatternArguments), (uu____2501)))
in (

let uu____2503 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error uu____2496 uu____2503)))
end)
end))))
end
| ((f1)::formals', ((p2, p_imp))::pats') -> begin
(match (f1) with
| (uu____2577, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____2578))) when p_imp -> begin
(

let uu____2581 = (aux formals' pats')
in (((p2), (true)))::uu____2581)
end
| (uu____2598, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p2.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p3 = (

let uu____2606 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (maybe_dot inaccessible a uu____2606))
in (

let uu____2607 = (aux formals' pats2)
in (((p3), (true)))::uu____2607)))
end
| (uu____2624, imp) -> begin
(

let uu____2630 = (

let uu____2637 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p2), (uu____2637)))
in (

let uu____2640 = (aux formals' pats')
in (uu____2630)::uu____2640))
end)
end))
in (

let uu___105_2655 = p1
in (

let uu____2658 = (

let uu____2659 = (

let uu____2672 = (aux f pats1)
in ((fv), (uu____2672)))
in FStar_Syntax_Syntax.Pat_cons (uu____2659))
in {FStar_Syntax_Syntax.v = uu____2658; FStar_Syntax_Syntax.p = uu___105_2655.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____2689 -> begin
p1
end)))
in (

let one_pat = (fun allow_wc_dependence env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____2731 = (pat_as_arg_with_env allow_wc_dependence env1 p2)
in (match (uu____2731) with
| (b, a, w, env2, arg, guard, p3) -> begin
(

let uu____2789 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____2789) with
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2815 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in (FStar_Errors.raise_error uu____2815 p3.FStar_Syntax_Syntax.p))
end
| uu____2838 -> begin
((b), (a), (w), (arg), (guard), (p3))
end))
end))))
in (

let uu____2847 = (one_pat true env p)
in (match (uu____2847) with
| (b, uu____2877, uu____2878, tm, guard, p1) -> begin
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
| (uu____2936, FStar_Syntax_Syntax.Tm_uinst (e2, uu____2938)) -> begin
(aux p1 e2)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____2943), uu____2944) -> begin
(pkg p1.FStar_Syntax_Syntax.v)
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____2948 = (

let uu____2949 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2950 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2949 uu____2950)))
in (failwith uu____2948))
end
| uu____2951 -> begin
()
end);
(

let uu____2953 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____2953) with
| true -> begin
(

let uu____2954 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2955 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____2954 uu____2955)))
end
| uu____2956 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___106_2959 = x
in {FStar_Syntax_Syntax.ppname = uu___106_2959.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___106_2959.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____2963 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____2963) with
| true -> begin
(

let uu____2964 = (

let uu____2965 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2966 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2965 uu____2966)))
in (failwith uu____2964))
end
| uu____2967 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___107_2970 = x
in {FStar_Syntax_Syntax.ppname = uu___107_2970.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_2970.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____2972), uu____2973) -> begin
(pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e1)))))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____2995 = (

let uu____2996 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____2996)))
in (match (uu____2995) with
| true -> begin
(

let uu____2997 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2997))
end
| uu____2998 -> begin
()
end));
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____3016; FStar_Syntax_Syntax.vars = uu____3017}, args)) -> begin
((

let uu____3056 = (

let uu____3057 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____3057 Prims.op_Negation))
in (match (uu____3056) with
| true -> begin
(

let uu____3058 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3058))
end
| uu____3059 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____3200))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3275)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3312) -> begin
(

let pat = (

let uu____3334 = (aux argpat e2)
in (

let uu____3335 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3334), (uu____3335))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3340 -> begin
(

let uu____3363 = (

let uu____3364 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3365 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3364 uu____3365)))
in (failwith uu____3363))
end))
in (match_args [] args argpats)));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____3377; FStar_Syntax_Syntax.vars = uu____3378}, uu____3379); FStar_Syntax_Syntax.pos = uu____3380; FStar_Syntax_Syntax.vars = uu____3381}, args)) -> begin
((

let uu____3424 = (

let uu____3425 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____3425 Prims.op_Negation))
in (match (uu____3424) with
| true -> begin
(

let uu____3426 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3426))
end
| uu____3427 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____3568))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3643)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3680) -> begin
(

let pat = (

let uu____3702 = (aux argpat e2)
in (

let uu____3703 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3702), (uu____3703))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3708 -> begin
(

let uu____3731 = (

let uu____3732 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3733 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3732 uu____3733)))
in (failwith uu____3731))
end))
in (match_args [] args argpats)));
)
end
| uu____3742 -> begin
(

let uu____3747 = (

let uu____3748 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____3749 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____3750 = (FStar_Syntax_Print.term_to_string exp)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____3748 uu____3749 uu____3750))))
in (failwith uu____3747))
end))))
in (aux p exp))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____3793 -> (match (uu____3793) with
| (p, i) -> begin
(

let uu____3810 = (decorated_pattern_as_term p)
in (match (uu____3810) with
| (vars, te) -> begin
(

let uu____3833 = (

let uu____3838 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____3838)))
in ((vars), (uu____3833)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____3852 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____3852)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____3856 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____3856)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____3860 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____3860)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____3881 = (

let uu____3896 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____3896 FStar_List.unzip))
in (match (uu____3881) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____4006 = (

let uu____4007 = (

let uu____4008 = (

let uu____4023 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____4023), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____4008))
in (mk1 uu____4007))
in ((vars1), (uu____4006))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let comp_univ_opt : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____4055, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.GTotal (uu____4065, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::uu____4079 -> begin
FStar_Pervasives_Native.Some (hd1)
end)
end))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____4105))::[] -> begin
wp
end
| uu____4122 -> begin
(

let uu____4131 = (

let uu____4132 = (

let uu____4133 = (FStar_List.map (fun uu____4143 -> (match (uu____4143) with
| (x, uu____4149) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____4133 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____4132))
in (failwith uu____4131))
end)
in (

let uu____4154 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____4154), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____4174 = (destruct_comp c)
in (match (uu____4174) with
| (u, uu____4182, wp) -> begin
(

let uu____4184 = (

let uu____4193 = (

let uu____4194 = (lift.FStar_TypeChecker_Env.mlift_wp u c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____4194))
in (uu____4193)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____4184; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____4210 = (

let uu____4217 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____4218 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____4217 uu____4218)))
in (match (uu____4210) with
| (m, uu____4220, uu____4221) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____4237 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____4237) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____4238 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____4280 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____4280) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____4317 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____4317) with
| (a, kwp) -> begin
(

let uu____4348 = (destruct_comp m1)
in (

let uu____4355 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____4348), (uu____4355))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags1 -> (

let uu____4435 = (

let uu____4436 = (

let uu____4445 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4445)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____4436; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp uu____4435)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags1 -> (

let uu____4499 = (FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)
in (match (uu____4499) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____4500 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1)
end)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu____4511 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4511 lc.FStar_Syntax_Syntax.cflags (fun uu____4514 -> (

let uu____4515 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Subst.subst_comp subst1 uu____4515))))))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4521 = (

let uu____4522 = (FStar_Syntax_Subst.compress t)
in uu____4522.FStar_Syntax_Syntax.n)
in (match (uu____4521) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4525) -> begin
true
end
| uu____4538 -> begin
false
end)))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (reason1) -> begin
(

let uu____4593 = (

let uu____4594 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____4594))
in (match (uu____4593) with
| true -> begin
f
end
| uu____4595 -> begin
(

let uu____4596 = (reason1 ())
in (label uu____4596 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___108_4613 = g
in (

let uu____4614 = (

let uu____4615 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____4615))
in {FStar_TypeChecker_Env.guard_f = uu____4614; FStar_TypeChecker_Env.deferred = uu___108_4613.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___108_4613.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___108_4613.FStar_TypeChecker_Env.implicits}))
end))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____4635 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4635) with
| true -> begin
c
end
| uu____4636 -> begin
(

let uu____4637 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4637) with
| true -> begin
c
end
| uu____4638 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____4686 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4686)::[])
in (

let us = (

let uu____4690 = (

let uu____4693 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____4693)::[])
in (u_res)::uu____4690)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____4697 = (

let uu____4702 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____4703 = (

let uu____4704 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4705 = (

let uu____4708 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____4709 = (

let uu____4712 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____4712)::[])
in (uu____4708)::uu____4709))
in (uu____4704)::uu____4705))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4702 uu____4703)))
in (uu____4697 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4716 = (destruct_comp c1)
in (match (uu____4716) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end)))


let close_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____4749 -> (

let uu____4750 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (close_comp env bvs uu____4750)))))


let should_not_inline_lc : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___81_4759 -> (match (uu___81_4759) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____4760 -> begin
false
end)))))


let should_return : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun env eopt lc -> (match (eopt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (e) -> begin
((((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) && (

let uu____4782 = (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____4782)))) && (

let uu____4789 = (FStar_Syntax_Util.head_and_args' e)
in (match (uu____4789) with
| (head1, uu____4803) -> begin
(

let uu____4820 = (

let uu____4821 = (FStar_Syntax_Util.un_uinst head1)
in uu____4821.FStar_Syntax_Syntax.n)
in (match (uu____4820) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____4825 = (

let uu____4826 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_irreducible env uu____4826))
in (not (uu____4825)))
end
| uu____4827 -> begin
true
end))
end))) && (

let uu____4829 = (should_not_inline_lc lc)
in (not (uu____4829))))
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env u_t_opt t v1 -> (

let c = (

let uu____4855 = (

let uu____4856 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____4856))
in (match (uu____4855) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____4857 -> begin
(

let uu____4858 = (FStar_Syntax_Util.is_unit t)
in (match (uu____4858) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero)))
end
| uu____4859 -> begin
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

let uu____4864 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4864) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____4865 -> begin
(

let uu____4866 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____4866) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____4874 = (

let uu____4875 = (

let uu____4880 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____4881 = (

let uu____4882 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____4883 = (

let uu____4886 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____4886)::[])
in (uu____4882)::uu____4883))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4880 uu____4881)))
in (uu____4875 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env uu____4874)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
end))
in ((

let uu____4890 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____4890) with
| true -> begin
(

let uu____4891 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____4892 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____4893 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4891 uu____4892 uu____4893))))
end
| uu____4894 -> begin
()
end));
c;
)))


let weaken_flags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags1 -> (

let uu____4906 = (FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___82_4910 -> (match (uu___82_4910) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____4911 -> begin
false
end))))
in (match (uu____4906) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____4914 -> begin
(FStar_All.pipe_right flags1 (FStar_List.collect (fun uu___83_4920 -> (match (uu___83_4920) with
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

let uu____4939 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4939) with
| true -> begin
c
end
| uu____4940 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4942 = (destruct_comp c1)
in (match (uu____4942) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____4956 = (

let uu____4961 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____4962 = (

let uu____4963 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4964 = (

let uu____4967 = (FStar_Syntax_Syntax.as_arg formula)
in (

let uu____4968 = (

let uu____4971 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4971)::[])
in (uu____4967)::uu____4968))
in (uu____4963)::uu____4964))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4961 uu____4962)))
in (uu____4956 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (

let uu____4974 = (weaken_flags c1.FStar_Syntax_Syntax.flags)
in (mk_comp md u_res_t res_t wp1 uu____4974))))
end)))
end)))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____4997 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let uu____4999 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4999) with
| true -> begin
c
end
| uu____5000 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(weaken_comp env c f1)
end)
end))))
in (

let uu____5002 = (weaken_flags lc.FStar_Syntax_Syntax.cflags)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ uu____5002 weaken))))


let strengthen_comp : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun env reason c f flags1 -> (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____5043 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____5045 = (destruct_comp c1)
in (match (uu____5045) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5059 = (

let uu____5064 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____5065 = (

let uu____5066 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5067 = (

let uu____5070 = (

let uu____5071 = (

let uu____5072 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____5072 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5071))
in (

let uu____5073 = (

let uu____5076 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5076)::[])
in (uu____5070)::uu____5073))
in (uu____5066)::uu____5067))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5064 uu____5065)))
in (uu____5059 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 flags1)))
end)))
end))


let strengthen_precondition : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e_for_debug_only lc g0 -> (

let uu____5121 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____5121) with
| true -> begin
((lc), (g0))
end
| uu____5126 -> begin
(

let flags1 = (

let uu____5130 = (

let uu____5137 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____5137) with
| true -> begin
((true), ((FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]))
end
| uu____5146 -> begin
((false), ([]))
end))
in (match (uu____5130) with
| (maybe_trivial_post, flags1) -> begin
(

let uu____5157 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___84_5165 -> (match (uu___84_5165) with
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
| uu____5168 -> begin
[]
end))))
in (FStar_List.append flags1 uu____5157))
end))
in (

let strengthen = (fun uu____5174 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____5176 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____5178 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____5178) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____5181 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5181) with
| true -> begin
(

let uu____5182 = (FStar_TypeChecker_Normalize.term_to_string env e_for_debug_only)
in (

let uu____5183 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____5182 uu____5183)))
end
| uu____5184 -> begin
()
end));
(strengthen_comp env reason c f flags1);
)
end)))
end)))
in (

let uu____5185 = (

let uu____5186 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____5186 lc.FStar_Syntax_Syntax.res_typ flags1 strengthen))
in ((uu____5185), ((

let uu___109_5188 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___109_5188.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___109_5188.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___109_5188.FStar_TypeChecker_Env.implicits}))))))
end)))


let lcomp_has_trivial_postcondition : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) || (FStar_Util.for_some (fun uu___85_5195 -> (match (uu___85_5195) with
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
true
end
| uu____5196 -> begin
false
end)) lc.FStar_Syntax_Syntax.cflags)))


let maybe_add_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env uopt lc e -> (

let uu____5221 = ((FStar_Syntax_Util.is_lcomp_partial_return lc) || env.FStar_TypeChecker_Env.lax)
in (match (uu____5221) with
| true -> begin
e
end
| uu____5222 -> begin
(

let uu____5223 = ((lcomp_has_trivial_postcondition lc) && (

let uu____5225 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____5225)))
in (match (uu____5223) with
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
| uu____5246 -> begin
e
end))
end)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____5273 -> (match (uu____5273) with
| (b, lc2) -> begin
(

let debug1 = (fun f -> (

let uu____5293 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____5293) with
| true -> begin
(f ())
end
| uu____5294 -> begin
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

let uu____5301 = ((should_not_inline_lc lc11) || (should_not_inline_lc lc21))
in (match (uu____5301) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____5304 -> begin
(

let flags1 = (

let uu____5308 = (FStar_Syntax_Util.is_total_lcomp lc11)
in (match (uu____5308) with
| true -> begin
(

let uu____5311 = (FStar_Syntax_Util.is_total_lcomp lc21)
in (match (uu____5311) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____5314 -> begin
(

let uu____5315 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
in (match (uu____5315) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5318 -> begin
[]
end))
end))
end
| uu____5319 -> begin
(

let uu____5320 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) && (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21))
in (match (uu____5320) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5323 -> begin
[]
end))
end))
in (

let uu____5324 = (lcomp_has_trivial_postcondition lc21)
in (match (uu____5324) with
| true -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::flags1
end
| uu____5327 -> begin
flags1
end)))
end))
in (

let bind_it = (fun uu____5333 -> (

let uu____5334 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5334) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____5336 -> begin
(

let c1 = (FStar_Syntax_Syntax.lcomp_comp lc11)
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp lc21)
in ((debug1 (fun uu____5348 -> (

let uu____5349 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____5350 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____5352 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n" uu____5349 uu____5350 uu____5352))))));
(

let aux = (fun uu____5366 -> (

let uu____5367 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____5367) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____5388) -> begin
(

let uu____5389 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____5389) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____5402 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____5407 -> begin
(

let uu____5408 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____5408) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____5421 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun e1opt1 reason -> (match (((e1opt1), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____5479 = (

let uu____5484 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____5484), (reason)))
in FStar_Util.Inl (uu____5479))
end
| uu____5491 -> begin
(aux ())
end))
in (

let try_simplify = (fun uu____5515 -> (

let rec maybe_close = (fun t x c -> (

let uu____5532 = (

let uu____5533 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in uu____5533.FStar_Syntax_Syntax.n)
in (match (uu____5532) with
| FStar_Syntax_Syntax.Tm_refine (y, uu____5537) -> begin
(maybe_close y.FStar_Syntax_Syntax.sort x c)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____5543 -> begin
c
end)))
in (

let uu____5544 = (

let uu____5545 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____5545))
in (match (uu____5544) with
| true -> begin
(

let uu____5556 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____5556) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____5569 -> begin
(

let uu____5570 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonTrivialPreConditionInPrims), ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")) uu____5570))
end))
end
| uu____5579 -> begin
(

let uu____5580 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____5580) with
| true -> begin
(subst_c2 e1opt "both total")
end
| uu____5589 -> begin
(

let uu____5590 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____5590) with
| true -> begin
(

let uu____5599 = (

let uu____5604 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____5604), ("both gtot")))
in FStar_Util.Inl (uu____5599))
end
| uu____5609 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____5628 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____5630 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____5630))))
in (match (uu____5628) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___110_5641 = x
in {FStar_Syntax_Syntax.ppname = uu___110_5641.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_5641.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____5642 = (

let uu____5647 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____5647), ("c1 Tot")))
in FStar_Util.Inl (uu____5642))))
end
| uu____5652 -> begin
(aux ())
end))
end
| uu____5653 -> begin
(aux ())
end)
end))
end))
end))))
in (

let uu____5662 = (try_simplify ())
in (match (uu____5662) with
| FStar_Util.Inl (c, reason) -> begin
((debug1 (fun uu____5682 -> (

let uu____5683 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "(2) bind: Simplified (because %s) to\n\t%s\n" reason uu____5683))));
c;
)
end
| FStar_Util.Inr (reason) -> begin
((debug1 (fun uu____5692 -> (FStar_Util.print1 "(2) bind: Not simplified because %s\n" reason)));
(

let mk_bind = (fun c11 b1 c21 -> (

let uu____5713 = (lift_and_destruct env c11 c21)
in (match (uu____5713) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b1) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5770 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____5770)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____5772 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5772)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____5787 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____5788 = (

let uu____5791 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____5792 = (

let uu____5795 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____5796 = (

let uu____5799 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____5800 = (

let uu____5803 = (

let uu____5804 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____5804))
in (uu____5803)::[])
in (uu____5799)::uu____5800))
in (uu____5795)::uu____5796))
in (uu____5791)::uu____5792))
in (uu____5787)::uu____5788))
in (

let wp = (

let uu____5808 = (

let uu____5813 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____5813 wp_args))
in (uu____5808 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (mk_comp md u_t2 t2 wp bind_flags))))))
end)))
in (

let mk_seq = (fun c11 b1 c21 -> (

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in (

let uu____5838 = (FStar_TypeChecker_Env.join env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____5838) with
| (m, uu____5846, lift2) -> begin
(

let c23 = (

let uu____5849 = (lift_comp c22 m lift2)
in (FStar_Syntax_Syntax.mk_Comp uu____5849))
in (

let uu____5850 = (destruct_comp c12)
in (match (uu____5850) with
| (u1, t1, wp1) -> begin
(

let md_pure_or_ghost = (FStar_TypeChecker_Env.get_effect_decl env c12.FStar_Syntax_Syntax.effect_name)
in (

let vc1 = (

let uu____5864 = (

let uu____5869 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u1)::[]) env md_pure_or_ghost md_pure_or_ghost.FStar_Syntax_Syntax.trivial)
in (

let uu____5870 = (

let uu____5871 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____5872 = (

let uu____5875 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____5875)::[])
in (uu____5871)::uu____5872))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5869 uu____5870)))
in (uu____5864 FStar_Pervasives_Native.None r1))
in (strengthen_comp env FStar_Pervasives_Native.None c23 vc1 bind_flags)))
end)))
end)))))
in (

let c1_typ = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____5882 = (destruct_comp c1_typ)
in (match (uu____5882) with
| (u_res_t1, res_t1, uu____5891) -> begin
(

let uu____5892 = ((FStar_Option.isSome b) && (should_return env e1opt lc11))
in (match (uu____5892) with
| true -> begin
(

let e1 = (FStar_Option.get e1opt)
in (

let x = (FStar_Option.get b)
in (

let uu____5895 = (FStar_Syntax_Util.is_partial_return c1)
in (match (uu____5895) with
| true -> begin
((debug1 (fun uu____5903 -> (

let uu____5904 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____5905 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case a): Substituting %s for %s" uu____5904 uu____5905)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (mk_bind c1 b c21));
)
end
| uu____5907 -> begin
(

let uu____5908 = (((FStar_Options.vcgen_optimize_bind_as_seq ()) && (lcomp_has_trivial_postcondition lc11)) && (

let uu____5910 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____5910)))
in (match (uu____5908) with
| true -> begin
(

let e1' = (

let uu____5932 = (FStar_Options.vcgen_decorate_with_type ())
in (match (uu____5932) with
| true -> begin
(FStar_Syntax_Util.mk_with_type u_res_t1 res_t1 e1)
end
| uu____5935 -> begin
e1
end))
in ((debug1 (fun uu____5943 -> (

let uu____5944 = (FStar_TypeChecker_Normalize.term_to_string env e1')
in (

let uu____5945 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case b): Substituting %s for %s" uu____5944 uu____5945)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1'))))::[]) c2)
in (mk_seq c1 b c21));
))
end
| uu____5949 -> begin
((debug1 (fun uu____5957 -> (

let uu____5958 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____5959 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case c): Adding equality %s = %s" uu____5958 uu____5959)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (

let x_eq_e = (

let uu____5962 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq2 u_res_t1 res_t1 e1 uu____5962))
in (

let c22 = (weaken_comp env c21 x_eq_e)
in (mk_bind c1 b c22))));
)
end))
end))))
end
| uu____5964 -> begin
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
| uu____5978 -> begin
g2
end))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let should_return1 = ((((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)) && (should_return env (FStar_Pervasives_Native.Some (e)) lc)) && (

let uu____6000 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____6000))))
in (

let flags1 = (match (should_return1) with
| true -> begin
(

let uu____6006 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____6006) with
| true -> begin
(FStar_Syntax_Syntax.RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____6009 -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end))
end
| uu____6010 -> begin
lc.FStar_Syntax_Syntax.cflags
end)
in (

let refine1 = (fun uu____6016 -> (

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

let uu____6020 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____6020) with
| true -> begin
(

let retc = (return_value env (FStar_Pervasives_Native.Some (u_t)) (FStar_Syntax_Util.comp_result c) e)
in (

let uu____6022 = (

let uu____6023 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____6023)))
in (match (uu____6022) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___111_6026 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___111_6026.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___111_6026.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___111_6026.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____6027 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags1)
end)))
end
| uu____6028 -> begin
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

let uu____6037 = (

let uu____6040 = (return_value env (FStar_Pervasives_Native.Some (u_t)) t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____6040 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6037))
in (

let eq1 = (FStar_Syntax_Util.mk_eq2 u_t t xexp e)
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____6045 = (

let uu____6046 = (

let uu____6047 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None uu____6047 ((FStar_Pervasives_Native.Some (x)), (eq_ret))))
in (FStar_Syntax_Syntax.lcomp_comp uu____6046))
in (FStar_Syntax_Util.comp_set_flags uu____6045 flags1))))))))))
end)))))
in (match ((not (should_return1))) with
| true -> begin
lc
end
| uu____6050 -> begin
(FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ flags1 refine1)
end)))))


let maybe_return_e2_and_bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r env e1opt lc1 e2 uu____6082 -> (match (uu____6082) with
| (x, lc2) -> begin
(

let lc21 = (

let eff1 = (FStar_TypeChecker_Env.norm_eff_name env lc1.FStar_Syntax_Syntax.eff_name)
in (

let eff2 = (FStar_TypeChecker_Env.norm_eff_name env lc2.FStar_Syntax_Syntax.eff_name)
in (

let uu____6094 = (((

let uu____6097 = (is_pure_or_ghost_effect env eff1)
in (not (uu____6097))) || (should_not_inline_lc lc1)) && (is_pure_or_ghost_effect env eff2))
in (match (uu____6094) with
| true -> begin
(maybe_assume_result_eq_pure_term env e2 lc2)
end
| uu____6098 -> begin
lc2
end))))
in (bind r env e1opt lc1 ((x), (lc21))))
end))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____6111 = (

let uu____6112 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____6112))
in (FStar_Syntax_Syntax.fvar uu____6111 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp)) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____6178 -> (match (uu____6178) with
| (uu____6191, eff_label, uu____6193, uu____6194) -> begin
(join_effects env eff eff_label)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let uu____6205 = (

let uu____6212 = (FStar_All.pipe_right lcases (FStar_Util.for_some (fun uu____6246 -> (match (uu____6246) with
| (uu____6259, uu____6260, flags1, uu____6262) -> begin
(FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___86_6276 -> (match (uu___86_6276) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____6277 -> begin
false
end))))
end))))
in (match (uu____6212) with
| true -> begin
((true), ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
end
| uu____6286 -> begin
((false), ([]))
end))
in (match (uu____6205) with
| (should_not_inline_whole_match, bind_cases_flags) -> begin
(

let bind_cases = (fun uu____6300 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____6302 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____6302) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____6303 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____6332 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____6333 = (

let uu____6338 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____6339 = (

let uu____6340 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____6341 = (

let uu____6344 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____6345 = (

let uu____6348 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____6349 = (

let uu____6352 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____6352)::[])
in (uu____6348)::uu____6349))
in (uu____6344)::uu____6345))
in (uu____6340)::uu____6341))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6338 uu____6339)))
in (uu____6333 FStar_Pervasives_Native.None uu____6332))))
in (

let default_case = (

let post_k = (

let uu____6359 = (

let uu____6366 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____6366)::[])
in (

let uu____6367 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____6359 uu____6367)))
in (

let kwp = (

let uu____6373 = (

let uu____6380 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____6380)::[])
in (

let uu____6381 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____6373 uu____6381)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____6386 = (

let uu____6387 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____6387)::[])
in (

let uu____6388 = (

let uu____6389 = (

let uu____6394 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____6394))
in (

let uu____6395 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____6389 uu____6395)))
in (FStar_Syntax_Util.abs uu____6386 uu____6388 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let maybe_return = (fun eff_label_then cthen -> (

let uu____6415 = (should_not_inline_whole_match || (

let uu____6417 = (is_pure_or_ghost_effect env eff)
in (not (uu____6417))))
in (match (uu____6415) with
| true -> begin
(cthen true)
end
| uu____6418 -> begin
(cthen false)
end)))
in (

let comp = (FStar_List.fold_right (fun uu____6450 celse -> (match (uu____6450) with
| (g, eff_label, uu____6466, cthen) -> begin
(

let uu____6478 = (

let uu____6503 = (

let uu____6504 = (maybe_return eff_label cthen)
in (FStar_Syntax_Syntax.lcomp_comp uu____6504))
in (lift_and_destruct env uu____6503 celse))
in (match (uu____6478) with
| ((md, uu____6506, uu____6507), (uu____6508, uu____6509, wp_then), (uu____6511, uu____6512, wp_else)) -> begin
(

let uu____6532 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____6532 []))
end))
end)) lcases default_case)
in (match (lcases) with
| [] -> begin
comp
end
| (uu____6546)::[] -> begin
comp
end
| uu____6586 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____6604 = (destruct_comp comp1)
in (match (uu____6604) with
| (uu____6611, uu____6612, wp) -> begin
(

let wp1 = (

let uu____6617 = (

let uu____6622 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____6623 = (

let uu____6624 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____6625 = (

let uu____6628 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6628)::[])
in (uu____6624)::uu____6625))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6622 uu____6623)))
in (uu____6617 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 bind_cases_flags))
end))))
end)))))
end))))
in (FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags bind_cases))
end))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____6663 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____6663) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6672 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____6677 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____6672 uu____6677)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_prop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let is_prop = (fun t1 -> (

let uu____6719 = (

let uu____6720 = (FStar_Syntax_Util.unrefine t1)
in uu____6720.FStar_Syntax_Syntax.n)
in (match (uu____6719) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.prop_lid)
end
| uu____6724 -> begin
false
end)))
in (

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____6732 = (

let uu____6733 = (FStar_Syntax_Subst.compress t2)
in uu____6733.FStar_Syntax_Syntax.n)
in (match (uu____6732) with
| FStar_Syntax_Syntax.Tm_type (uu____6736) -> begin
true
end
| uu____6737 -> begin
false
end))))
in (

let uu____6738 = (

let uu____6739 = (FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ)
in uu____6739.FStar_Syntax_Syntax.n)
in (match (uu____6738) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && ((is_prop t) || (is_type1 t))) -> begin
(

let uu____6747 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2p_lid)
in (

let b2p1 = (

let uu____6757 = (FStar_Ident.set_lid_range FStar_Parser_Const.b2p_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____6757 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let lc1 = (

let uu____6759 = (

let uu____6760 = (

let uu____6761 = (

let uu____6764 = (

let uu____6765 = (is_prop t)
in (match (uu____6765) with
| true -> begin
FStar_Syntax_Util.kprop
end
| uu____6766 -> begin
FStar_Syntax_Util.ktype0
end))
in (FStar_Syntax_Syntax.mk_Total uu____6764))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6761))
in ((FStar_Pervasives_Native.None), (uu____6760)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____6759))
in (

let e1 = (

let uu____6774 = (

let uu____6779 = (

let uu____6780 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6780)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2p1 uu____6779))
in (uu____6774 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____6785 -> begin
((e), (lc))
end)))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____6822 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____6822) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____6845 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____6867 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____6867), (false)))
end
| uu____6872 -> begin
(

let uu____6873 = (FStar_TypeChecker_Rel.get_subtyping_predicate env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____6873), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____6884) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____6893 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Errors.raise_error uu____6893 e.FStar_Syntax_Syntax.pos))
end
| uu____6904 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___112_6907 = lc
in {FStar_Syntax_Syntax.eff_name = uu___112_6907.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___112_6907.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___112_6907.FStar_Syntax_Syntax.comp_thunk})), (FStar_TypeChecker_Rel.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____6912 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____6912) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___113_6920 = lc
in {FStar_Syntax_Syntax.eff_name = uu___113_6920.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___113_6920.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___113_6920.FStar_Syntax_Syntax.comp_thunk})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___114_6923 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___114_6923.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___114_6923.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___114_6923.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____6929 -> (

let uu____6930 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____6930) with
| true -> begin
(FStar_Syntax_Syntax.lcomp_comp lc)
end
| uu____6931 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in (

let uu____6933 = (

let uu____6934 = (FStar_Syntax_Subst.compress f1)
in uu____6934.FStar_Syntax_Syntax.n)
in (match (uu____6933) with
| FStar_Syntax_Syntax.Tm_abs (uu____6937, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____6939; FStar_Syntax_Syntax.vars = uu____6940}, uu____6941) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___115_6963 = lc
in {FStar_Syntax_Syntax.eff_name = uu___115_6963.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___115_6963.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___115_6963.FStar_Syntax_Syntax.comp_thunk})
in (FStar_Syntax_Syntax.lcomp_comp lc1))
end
| uu____6964 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((

let uu____6967 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____6967) with
| true -> begin
(

let uu____6968 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____6969 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____6970 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____6971 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____6968 uu____6969 uu____6970 uu____6971)))))
end
| uu____6972 -> begin
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

let uu____6984 = (

let uu____6989 = (

let uu____6990 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____6990)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____6989))
in (uu____6984 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____6993 -> begin
f1
end)
in (

let uu____6994 = (

let uu____6999 = (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____7016 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____7017 = (FStar_Syntax_Util.lcomp_of_comp cret)
in (

let uu____7018 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____6999 uu____7016 e uu____7017 uu____7018)))))
in (match (uu____6994) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___116_7022 = x
in {FStar_Syntax_Syntax.ppname = uu___116_7022.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_7022.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____7024 = (FStar_Syntax_Util.lcomp_of_comp c)
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____7024 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((

let uu____7029 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____7029) with
| true -> begin
(

let uu____7030 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____7030))
end
| uu____7031 -> begin
()
end));
c2;
))))
end)))))));
))
end)))
end)))
in (

let flags1 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___87_7040 -> (match (uu___87_7040) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____7043 -> begin
[]
end))))
in (

let lc1 = (

let uu____7045 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____7045 t flags1 strengthen))
in (

let g2 = (

let uu___117_7047 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___117_7047.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___117_7047.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___117_7047.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____7078 = (

let uu____7079 = (

let uu____7084 = (

let uu____7085 = (

let uu____7086 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____7086))
in (uu____7085)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____7084))
in (uu____7079 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____7078))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____7095 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____7095) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____7106 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____7113) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____7128) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____7144 = ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))
in (match (uu____7144) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____7158))::((ens, uu____7160))::uu____7161 -> begin
(

let uu____7190 = (

let uu____7193 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____7193))
in (

let uu____7194 = (

let uu____7195 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____7195))
in ((uu____7190), (uu____7194))))
end
| uu____7198 -> begin
(

let uu____7207 = (

let uu____7212 = (

let uu____7213 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____7213))
in ((FStar_Errors.Fatal_EffectConstructorNotFullyApplied), (uu____7212)))
in (FStar_Errors.raise_error uu____7207 comp.FStar_Syntax_Syntax.pos))
end)
end
| uu____7220 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____7229))::uu____7230 -> begin
(

let uu____7249 = (

let uu____7254 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7254))
in (match (uu____7249) with
| (us_r, uu____7286) -> begin
(

let uu____7287 = (

let uu____7292 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7292))
in (match (uu____7287) with
| (us_e, uu____7324) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____7327 = (

let uu____7328 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar uu____7328 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7327 us_r))
in (

let as_ens = (

let uu____7330 = (

let uu____7331 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar uu____7331 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7330 us_e))
in (

let req = (

let uu____7335 = (

let uu____7340 = (

let uu____7341 = (

let uu____7352 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____7352)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____7341)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____7340))
in (uu____7335 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____7370 = (

let uu____7375 = (

let uu____7376 = (

let uu____7387 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____7387)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____7376)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____7375))
in (uu____7370 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____7402 = (

let uu____7405 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____7405))
in (

let uu____7406 = (

let uu____7407 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____7407))
in ((uu____7402), (uu____7406)))))))))
end))
end))
end
| uu____7410 -> begin
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

let uu____7440 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7440) with
| true -> begin
(

let uu____7441 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____7442 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____7441 uu____7442)))
end
| uu____7443 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____7466 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7466) with
| true -> begin
(

let uu____7467 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____7468 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____7467 uu____7468)))
end
| uu____7469 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____7475 = (

let uu____7476 = (

let uu____7477 = (FStar_Syntax_Subst.compress t)
in uu____7477.FStar_Syntax_Syntax.n)
in (match (uu____7476) with
| FStar_Syntax_Syntax.Tm_app (uu____7480) -> begin
false
end
| uu____7495 -> begin
true
end))
in (match (uu____7475) with
| true -> begin
t
end
| uu____7496 -> begin
(

let uu____7497 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____7497) with
| (head1, args) -> begin
(

let uu____7534 = (

let uu____7535 = (

let uu____7536 = (FStar_Syntax_Subst.compress head1)
in uu____7536.FStar_Syntax_Syntax.n)
in (match (uu____7535) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____7539 -> begin
false
end))
in (match (uu____7534) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____7561 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____7570 -> begin
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
| uu____7599 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____7606 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____7606) with
| (formals, uu____7620) -> begin
(

let n_implicits = (

let uu____7638 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____7714 -> (match (uu____7714) with
| (uu____7721, imp) -> begin
((Prims.op_Equality imp FStar_Pervasives_Native.None) || (Prims.op_Equality imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality))))
end))))
in (match (uu____7638) with
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

let uu____7854 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____7854) with
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

let uu____7878 = (

let uu____7883 = (

let uu____7884 = (FStar_Util.string_of_int n_expected)
in (

let uu____7891 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7892 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____7884 uu____7891 uu____7892))))
in ((FStar_Errors.Fatal_MissingImplicitArguments), (uu____7883)))
in (

let uu____7899 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____7878 uu____7899)))
end
| uu____7902 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___88_7922 -> (match (uu___88_7922) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7952 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7952) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_18), uu____8067) when (_0_18 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____8110, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____8143 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____8143) with
| (v1, uu____8183, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____8200 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____8200) with
| (args, bs3, subst3, g') -> begin
(

let uu____8293 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____8293)))
end)))
end)))
end
| (uu____8320, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____8366 = (

let uu____8393 = (inst_n_binders t)
in (aux [] uu____8393 bs1))
in (match (uu____8366) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____8464) -> begin
((e), (torig), (guard))
end
| (uu____8495, []) when (

let uu____8526 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____8526))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____8527 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____8559 -> begin
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
| uu____8574 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____8584 = (

let uu____8587 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____8587 (FStar_List.map (fun u -> (

let uu____8597 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____8597 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____8584 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____8618 = (FStar_Util.set_is_empty x)
in (match (uu____8618) with
| true -> begin
[]
end
| uu____8621 -> begin
(

let s = (

let uu____8625 = (

let uu____8628 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____8628))
in (FStar_All.pipe_right uu____8625 FStar_Util.set_elements))
in ((

let uu____8636 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8636) with
| true -> begin
(

let uu____8637 = (

let uu____8638 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____8638))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____8637))
end
| uu____8641 -> begin
()
end));
(

let r = (

let uu____8645 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____8645))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____8660 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8660) with
| true -> begin
(

let uu____8661 = (

let uu____8662 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____8662))
in (

let uu____8663 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____8664 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____8661 uu____8663 uu____8664))))
end
| uu____8665 -> begin
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

let uu____8690 = (FStar_Util.set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____8690 FStar_Util.set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____8728) -> begin
generalized_univ_names
end
| (uu____8735, []) -> begin
explicit_univ_names
end
| uu____8742 -> begin
(

let uu____8751 = (

let uu____8756 = (

let uu____8757 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____8757))
in ((FStar_Errors.Fatal_UnexpectedGeneralizedUniverse), (uu____8756)))
in (FStar_Errors.raise_error uu____8751 t.FStar_Syntax_Syntax.pos))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in ((

let uu____8775 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8775) with
| true -> begin
(

let uu____8776 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____8777 = (FStar_Syntax_Print.univ_names_to_string univnames1)
in (FStar_Util.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" uu____8776 uu____8777)))
end
| uu____8778 -> begin
()
end));
(

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____8783 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8783) with
| true -> begin
(

let uu____8784 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____8784))
end
| uu____8785 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____8790 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8790) with
| true -> begin
(

let uu____8791 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____8792 = (FStar_Syntax_Print.univ_names_to_string gen1)
in (FStar_Util.print2 "After generalization, t: %s and univs: %s\n" uu____8791 uu____8792)))
end
| uu____8793 -> begin
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

let uu____8868 = (

let uu____8869 = (FStar_Util.for_all (fun uu____8882 -> (match (uu____8882) with
| (uu____8891, uu____8892, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____8869))
in (match (uu____8868) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8932 -> begin
(

let norm1 = (fun c -> ((

let uu____8940 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8940) with
| true -> begin
(

let uu____8941 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____8941))
end
| uu____8942 -> begin
()
end));
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env c)
in ((

let uu____8945 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8945) with
| true -> begin
(

let uu____8946 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8946))
end
| uu____8947 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____9009 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____9009 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____9141 -> (match (uu____9141) with
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

let uu____9207 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9207) with
| true -> begin
(

let uu____9208 = (

let uu____9209 = (

let uu____9212 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____9212 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____9209 (FStar_String.concat ", ")))
in (

let uu____9239 = (

let uu____9240 = (

let uu____9243 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____9243 (FStar_List.map (fun uu____9271 -> (match (uu____9271) with
| (u, t2) -> begin
(

let uu____9278 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____9279 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s : %s)" uu____9278 uu____9279)))
end)))))
in (FStar_All.pipe_right uu____9240 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9208 uu____9239)))
end
| uu____9282 -> begin
()
end));
(

let univs2 = (

let uu____9286 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uu____9309 -> (match (uu____9309) with
| (uu____9318, t2) -> begin
(

let uu____9320 = (FStar_Syntax_Free.univs t2)
in (FStar_Util.set_union univs2 uu____9320))
end)) univs1 uu____9286))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____9343 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9343) with
| true -> begin
(

let uu____9344 = (

let uu____9345 = (

let uu____9348 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____9348 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____9345 (FStar_String.concat ", ")))
in (

let uu____9375 = (

let uu____9376 = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____9408 -> (match (uu____9408) with
| (u, t2) -> begin
(

let uu____9415 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____9416 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "(%s : %s)" uu____9415 uu____9416)))
end))))
in (FStar_All.pipe_right uu____9376 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____9344 uu____9375)))
end
| uu____9419 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
))))))
end))
in (

let uu____9446 = (

let uu____9479 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____9479))
in (match (uu____9446) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____9603 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____9603) with
| true -> begin
()
end
| uu____9604 -> begin
(

let uu____9605 = lec_hd
in (match (uu____9605) with
| (lb1, uu____9613, uu____9614) -> begin
(

let uu____9615 = lec2
in (match (uu____9615) with
| (lb2, uu____9623, uu____9624) -> begin
(

let msg = (

let uu____9626 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____9627 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____9626 uu____9627)))
in (

let uu____9628 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleSetOfUniverse), (msg)) uu____9628)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun uu____9749 -> (match (uu____9749) with
| (u, uu____9757) -> begin
(FStar_All.pipe_right u21 (FStar_Util.for_some (fun uu____9779 -> (match (uu____9779) with
| (u', uu____9787) -> begin
(FStar_Syntax_Unionfind.equiv u u')
end))))
end)))))
in (

let uu____9792 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____9792) with
| true -> begin
()
end
| uu____9793 -> begin
(

let uu____9794 = lec_hd
in (match (uu____9794) with
| (lb1, uu____9802, uu____9803) -> begin
(

let uu____9804 = lec2
in (match (uu____9804) with
| (lb2, uu____9812, uu____9813) -> begin
(

let msg = (

let uu____9815 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____9816 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____9815 uu____9816)))
in (

let uu____9817 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleNumberOfTypes), (msg)) uu____9817)))
end))
end))
end))))
in (

let lecs1 = (

let uu____9827 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____9886 = (univs_and_uvars_of_lec this_lec)
in (match (uu____9886) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____9827 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail1 = (fun k -> (

let uu____10043 = lec_hd
in (match (uu____10043) with
| (lbname, e, c) -> begin
(

let uu____10053 = (

let uu____10058 = (

let uu____10059 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____10060 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____10061 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____10059 uu____10060 uu____10061))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____10058)))
in (

let uu____10062 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____10053 uu____10062)))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun uu____10092 -> (match (uu____10092) with
| (u, k) -> begin
(

let uu____10105 = (FStar_Syntax_Unionfind.find u)
in (match (uu____10105) with
| FStar_Pervasives_Native.Some (uu____10114) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____10121 -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env k)
in (

let uu____10125 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____10125) with
| (bs, kres) -> begin
((

let uu____10163 = (

let uu____10164 = (

let uu____10167 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____10167))
in uu____10164.FStar_Syntax_Syntax.n)
in (match (uu____10163) with
| FStar_Syntax_Syntax.Tm_type (uu____10168) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____10172 = (

let uu____10173 = (FStar_Util.set_is_empty free)
in (not (uu____10173)))
in (match (uu____10172) with
| true -> begin
(fail1 kres)
end
| uu____10174 -> begin
()
end)))
end
| uu____10175 -> begin
(fail1 kres)
end));
(

let a = (

let uu____10177 = (

let uu____10180 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) uu____10180))
in (FStar_Syntax_Syntax.new_bv uu____10177 kres))
in (

let t = (

let uu____10184 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____10184 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
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

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____10303 -> (match (uu____10303) with
| (lbname, e, c) -> begin
(

let uu____10349 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____10418 -> begin
(

let uu____10433 = ((e), (c))
in (match (uu____10433) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____10470 -> (match (uu____10470) with
| (x, uu____10478) -> begin
(

let uu____10483 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____10483))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____10497 = (

let uu____10498 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____10498))
in (match (uu____10497) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____10501 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____10502 -> begin
e1
end)
in (

let t = (

let uu____10506 = (

let uu____10507 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____10507.FStar_Syntax_Syntax.n)
in (match (uu____10506) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____10530 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____10530) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____10545 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____10547 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____10547), (gen_tvars))))))))
end))
end)
in (match (uu____10349) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____10701 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____10701) with
| true -> begin
(

let uu____10702 = (

let uu____10703 = (FStar_List.map (fun uu____10716 -> (match (uu____10716) with
| (lb, uu____10724, uu____10725) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____10703 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____10702))
end
| uu____10728 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____10746 -> (match (uu____10746) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____10775 = (gen env is_rec lecs)
in (match (uu____10775) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____10874 -> (match (uu____10874) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____10936 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____10936) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____10980 -> (match (uu____10980) with
| (l, us, e, c, gvs) -> begin
(

let uu____11014 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____11015 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____11016 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____11017 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11018 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____11014 uu____11015 uu____11016 uu____11017 uu____11018))))))
end))))
end
| uu____11019 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____11059 -> (match (uu____11059) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____11103 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____11103), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check1 = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____11159 -> begin
(

let uu____11160 = (FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21)
in (match (uu____11160) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____11166 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) uu____11166))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____11175 = (

let uu____11176 = (FStar_Syntax_Subst.compress e1)
in uu____11176.FStar_Syntax_Syntax.n)
in (match (uu____11175) with
| FStar_Syntax_Syntax.Tm_name (uu____11179) -> begin
true
end
| uu____11180 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___118_11200 = x
in {FStar_Syntax_Syntax.ppname = uu___118_11200.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_11200.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____11201 -> begin
e2
end)))
in (

let env2 = (

let uu___119_11203 = env1
in (

let uu____11204 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___119_11203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_11203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_11203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_11203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_11203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_11203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_11203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_11203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_11203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_11203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_11203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_11203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_11203.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_11203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_11203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____11204; FStar_TypeChecker_Env.is_iface = uu___119_11203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_11203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___119_11203.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___119_11203.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___119_11203.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___119_11203.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___119_11203.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___119_11203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_11203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___119_11203.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_11203.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___119_11203.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___119_11203.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___119_11203.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___119_11203.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___119_11203.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___119_11203.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___119_11203.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___119_11203.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___119_11203.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___119_11203.FStar_TypeChecker_Env.dep_graph}))
in (

let uu____11205 = (check1 env2 t1 t2)
in (match (uu____11205) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11212 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____11217 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____11212 uu____11217)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____11224 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____11224) with
| true -> begin
(

let uu____11225 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____11225))
end
| uu____11226 -> begin
()
end));
(

let uu____11227 = (decorate e t2)
in ((uu____11227), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____11263 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____11263) with
| true -> begin
(

let uu____11268 = (discharge g1)
in (

let uu____11269 = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((uu____11268), (uu____11269))))
end
| uu____11270 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]
in (

let c1 = (

let uu____11276 = (

let uu____11277 = (

let uu____11278 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____11278 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____11277 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____11276 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11280 = (destruct_comp c1)
in (match (uu____11280) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____11297 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____11298 = (

let uu____11303 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____11304 = (

let uu____11305 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____11306 = (

let uu____11309 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____11309)::[])
in (uu____11305)::uu____11306))
in (FStar_Syntax_Syntax.mk_Tm_app uu____11303 uu____11304)))
in (uu____11298 FStar_Pervasives_Native.None uu____11297)))
in ((

let uu____11313 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____11313) with
| true -> begin
(

let uu____11314 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____11314))
end
| uu____11315 -> begin
()
end));
(

let g2 = (

let uu____11317 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____11317))
in (

let uu____11318 = (discharge g2)
in (

let uu____11319 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____11318), (uu____11319)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___89_11351 -> (match (uu___89_11351) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____11359))::[] -> begin
(f fst1)
end
| uu____11376 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____11383 = (FStar_Syntax_Util.b2p e)
in (FStar_All.pipe_right uu____11383 (fun _0_21 -> FStar_TypeChecker_Common.NonTrivial (_0_21)))))
in (

let op_or_e = (fun e -> (

let uu____11394 = (

let uu____11397 = (FStar_Syntax_Util.b2p e)
in (FStar_Syntax_Util.mk_neg uu____11397))
in (FStar_All.pipe_right uu____11394 (fun _0_22 -> FStar_TypeChecker_Common.NonTrivial (_0_22)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_23 -> FStar_TypeChecker_Common.NonTrivial (_0_23))))
in (

let op_or_t = (fun t -> (

let uu____11412 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____11412 (fun _0_24 -> FStar_TypeChecker_Common.NonTrivial (_0_24)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_25 -> FStar_TypeChecker_Common.NonTrivial (_0_25))))
in (

let short_op_ite = (fun uu___90_11430 -> (match (uu___90_11430) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____11438))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____11457))::[] -> begin
(

let uu____11486 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____11486 (fun _0_26 -> FStar_TypeChecker_Common.NonTrivial (_0_26))))
end
| uu____11491 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____11502 = (

let uu____11510 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____11510)))
in (

let uu____11518 = (

let uu____11528 = (

let uu____11536 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____11536)))
in (

let uu____11544 = (

let uu____11554 = (

let uu____11562 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____11562)))
in (

let uu____11570 = (

let uu____11580 = (

let uu____11588 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____11588)))
in (

let uu____11596 = (

let uu____11606 = (

let uu____11614 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____11614)))
in (uu____11606)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____11580)::uu____11596))
in (uu____11554)::uu____11570))
in (uu____11528)::uu____11544))
in (uu____11502)::uu____11518))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11676 = (FStar_Util.find_map table (fun uu____11691 -> (match (uu____11691) with
| (x, mk1) -> begin
(

let uu____11708 = (FStar_Ident.lid_equals x lid)
in (match (uu____11708) with
| true -> begin
(

let uu____11711 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____11711))
end
| uu____11712 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (uu____11676) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____11714 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____11720 = (

let uu____11721 = (FStar_Syntax_Util.un_uinst l)
in uu____11721.FStar_Syntax_Syntax.n)
in (match (uu____11720) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____11725 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____11755))::uu____11756 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____11767 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____11774, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11775))))::uu____11776 -> begin
bs
end
| uu____11793 -> begin
(

let uu____11794 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____11794) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____11798 = (

let uu____11799 = (FStar_Syntax_Subst.compress t)
in uu____11799.FStar_Syntax_Syntax.n)
in (match (uu____11798) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____11803) -> begin
(

let uu____11820 = (FStar_Util.prefix_until (fun uu___91_11860 -> (match (uu___91_11860) with
| (uu____11867, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11868))) -> begin
false
end
| uu____11871 -> begin
true
end)) bs')
in (match (uu____11820) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____11906, uu____11907) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____11979, uu____11980) -> begin
(

let uu____12053 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____12071 -> (match (uu____12071) with
| (x, uu____12079) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____12053) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____12126 -> (match (uu____12126) with
| (x, i) -> begin
(

let uu____12145 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____12145), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____12154 -> begin
bs
end))
end))
end
| uu____12155 -> begin
bs
end))
end))
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 t -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in (

let uu____12183 = (((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1)))
in (match (uu____12183) with
| true -> begin
e
end
| uu____12184 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end)))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____12206 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____12206) with
| true -> begin
e
end
| uu____12207 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____12237 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____12237) with
| true -> begin
((

let uu____12239 = (FStar_Ident.text_of_lid lident)
in (d uu____12239));
(

let uu____12240 = (FStar_Ident.text_of_lid lident)
in (

let uu____12241 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" uu____12240 uu____12241)));
)
end
| uu____12242 -> begin
()
end));
(

let fv = (

let uu____12244 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____12244 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (((FStar_Syntax_Util.mk_letbinding lbname [] FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def [] FStar_Range.dummyRange))::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____12254 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___120_12260 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___120_12260.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___120_12260.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___120_12260.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___120_12260.FStar_Syntax_Syntax.sigattrs})), (uu____12254)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (

let visibility = (fun uu___92_12276 -> (match (uu___92_12276) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____12277 -> begin
false
end))
in (

let reducibility = (fun uu___93_12283 -> (match (uu___93_12283) with
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
| uu____12284 -> begin
false
end))
in (

let assumption = (fun uu___94_12290 -> (match (uu___94_12290) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____12291 -> begin
false
end))
in (

let reification = (fun uu___95_12297 -> (match (uu___95_12297) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____12298) -> begin
true
end
| uu____12299 -> begin
false
end))
in (

let inferred = (fun uu___96_12305 -> (match (uu___96_12305) with
| FStar_Syntax_Syntax.Discriminator (uu____12306) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____12307) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____12312) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____12321) -> begin
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
| uu____12330 -> begin
false
end))
in (

let has_eq = (fun uu___97_12336 -> (match (uu___97_12336) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____12337 -> begin
false
end))
in (

let quals_combo_ok = (fun quals q -> (match (q) with
| FStar_Syntax_Syntax.Assumption -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((Prims.op_Equality x q) || (inferred x)) || (visibility x)) || (assumption x)) || (env.FStar_TypeChecker_Env.is_iface && (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction))) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)))))
end
| FStar_Syntax_Syntax.New -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((Prims.op_Equality x q) || (inferred x)) || (visibility x)) || (assumption x)))))
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((Prims.op_Equality x q) || (visibility x)) || (reducibility x)) || (reification x)) || (inferred x)) || (env.FStar_TypeChecker_Env.is_iface && (Prims.op_Equality x FStar_Syntax_Syntax.Assumption))) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)))))
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Visible_default -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Irreducible -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Abstract -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Noeq -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Unopteq -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Abstract)) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (has_eq x)) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.TotalEffect -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((Prims.op_Equality x q) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Reifiable -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Reflectable (uu____12397) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____12402 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____12406 = (

let uu____12407 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___98_12411 -> (match (uu___98_12411) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____12412 -> begin
false
end))))
in (FStar_All.pipe_right uu____12407 Prims.op_Negation))
in (match (uu____12406) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____12427 = (

let uu____12432 = (

let uu____12433 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____12433 msg))
in ((FStar_Errors.Fatal_QulifierListNotPermitted), (uu____12432)))
in (FStar_Errors.raise_error uu____12427 r)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____12445 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____12447 -> begin
()
end);
(

let uu____12449 = (

let uu____12450 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____12450)))
in (match (uu____12449) with
| true -> begin
(err "ill-formed combination")
end
| uu____12453 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____12455), uu____12456) -> begin
((

let uu____12472 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____12472) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____12475 -> begin
()
end));
(

let uu____12476 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____12476) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____12481 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____12482) -> begin
(

let uu____12491 = (

let uu____12492 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____12492)))
in (match (uu____12491) with
| true -> begin
(err'1 ())
end
| uu____12497 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____12498) -> begin
(

let uu____12505 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____12505) with
| true -> begin
(err'1 ())
end
| uu____12508 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____12509) -> begin
(

let uu____12516 = (

let uu____12517 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____12517)))
in (match (uu____12516) with
| true -> begin
(err'1 ())
end
| uu____12522 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____12523) -> begin
(

let uu____12524 = (

let uu____12525 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____12525)))
in (match (uu____12524) with
| true -> begin
(err'1 ())
end
| uu____12530 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12531) -> begin
(

let uu____12532 = (

let uu____12533 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____12533)))
in (match (uu____12532) with
| true -> begin
(err'1 ())
end
| uu____12538 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____12539) -> begin
(

let uu____12552 = (

let uu____12553 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____12553)))
in (match (uu____12552) with
| true -> begin
(err'1 ())
end
| uu____12558 -> begin
()
end))
end
| uu____12559 -> begin
()
end);
))))))
end
| uu____12560 -> begin
()
end)))))))))))


let must_erase_for_extraction : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun g t -> (

let rec aux_whnf = (fun env t1 -> (

let uu____12593 = (

let uu____12594 = (FStar_Syntax_Subst.compress t1)
in uu____12594.FStar_Syntax_Syntax.n)
in (match (uu____12593) with
| FStar_Syntax_Syntax.Tm_type (uu____12597) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (

let uu____12600 = (

let uu____12605 = (FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv)
in (FStar_All.pipe_right uu____12605 (FStar_TypeChecker_Env.lookup_attrs_of_lid g)))
in (FStar_All.pipe_right uu____12600 (fun l_opt -> ((FStar_Util.is_some l_opt) && (

let uu____12623 = (FStar_All.pipe_right l_opt FStar_Util.must)
in (FStar_All.pipe_right uu____12623 (FStar_List.existsb (fun t2 -> (

let uu____12640 = (

let uu____12641 = (FStar_Syntax_Subst.compress t2)
in uu____12641.FStar_Syntax_Syntax.n)
in (match (uu____12640) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_Ident.lid_equals fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.must_erase_for_extraction_attr) -> begin
true
end
| uu____12645 -> begin
false
end)))))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____12646) -> begin
(

let uu____12659 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____12659) with
| (bs, c) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____12685 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____12685) with
| true -> begin
(aux env1 (FStar_Syntax_Util.comp_result c))
end
| uu____12686 -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____12687; FStar_Syntax_Syntax.index = uu____12688; FStar_Syntax_Syntax.sort = t2}, uu____12690) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____12698, uu____12699) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____12741)::[]) -> begin
(

let uu____12772 = (

let uu____12773 = (FStar_Syntax_Util.un_uinst head1)
in uu____12773.FStar_Syntax_Syntax.n)
in (match (uu____12772) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
end
| uu____12777 -> begin
false
end))
end
| uu____12778 -> begin
false
end)))
and aux = (fun env t1 -> (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Iota)::[]) env t1)
in (

let res = (aux_whnf env t2)
in ((

let uu____12786 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Extraction")))
in (match (uu____12786) with
| true -> begin
(

let uu____12787 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "must_erase=%s: %s\n" (match (res) with
| true -> begin
"true"
end
| uu____12788 -> begin
"false"
end) uu____12787))
end
| uu____12789 -> begin
()
end));
res;
))))
in (aux g t)))




