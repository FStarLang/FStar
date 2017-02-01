
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


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun uu___90_64 -> (match (uu___90_64) with
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

let uu___110_181 = FStar_TypeChecker_Rel.trivial_guard
in (

let uu____182 = (

let uu____190 = (

let uu____197 = (as_uvar u)
in ((reason), (env), (uu____197), (t), (k), (r)))
in (uu____190)::[])
in {FStar_TypeChecker_Env.guard_f = uu___110_181.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___110_181.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___110_181.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____182}))
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
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____342; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((match ((univ_vars <> [])) with
| true -> begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end
| uu____363 -> begin
()
end);
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (

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

let t = (

let uu____388 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right uu____388 Prims.fst))
in (((

let uu___111_393 = a
in {FStar_Syntax_Syntax.ppname = uu___111_393.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___111_393.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
end))
end
| uu____394 -> begin
((a), (true))
end)))
in (

let rec aux = (fun must_check_ty vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, uu____419) -> begin
(aux must_check_ty vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, uu____426) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____453) -> begin
(

let uu____476 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____500 uu____501 -> (match (((uu____500), (uu____501))) with
| ((scope, bs, must_check_ty), (a, imp)) -> begin
(

let uu____543 = (match (must_check_ty) with
| true -> begin
((a), (true))
end
| uu____548 -> begin
(mk_binder scope a)
end)
in (match (uu____543) with
| (tb, must_check_ty) -> begin
(

let b = ((tb), (imp))
in (

let bs = (FStar_List.append bs ((b)::[]))
in (

let scope = (FStar_List.append scope ((b)::[]))
in ((scope), (bs), (must_check_ty)))))
end))
end)) ((vars), ([]), (must_check_ty))))
in (match (uu____476) with
| (scope, bs, must_check_ty) -> begin
(

let uu____604 = (aux must_check_ty scope body)
in (match (uu____604) with
| (res, must_check_ty) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t) -> begin
(

let uu____621 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)
in (match (uu____621) with
| None -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____623 -> begin
(FStar_Syntax_Util.ml_comp t r)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t = (FStar_Syntax_Util.arrow bs c)
in ((

let uu____630 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____630) with
| true -> begin
(

let uu____631 = (FStar_Range.string_of_range r)
in (

let uu____632 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____633 = (FStar_Util.string_of_bool must_check_ty)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" uu____631 uu____632 uu____633))))
end
| uu____634 -> begin
()
end));
((FStar_Util.Inl (t)), (must_check_ty));
)))
end))
end))
end
| uu____641 -> begin
(match (must_check_ty) with
| true -> begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end
| uu____648 -> begin
(

let uu____649 = (

let uu____652 = (

let uu____653 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____653 Prims.fst))
in FStar_Util.Inl (uu____652))
in ((uu____649), (false)))
end)
end)))
in (

let uu____660 = (

let uu____665 = (t_binders env)
in (aux false uu____665 e))
in (match (uu____660) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(

let uu____682 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____682) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____685 -> begin
(

let uu____686 = (

let uu____687 = (

let uu____690 = (

let uu____691 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____691))
in ((uu____690), (rng)))
in FStar_Errors.Error (uu____687))
in (Prims.raise uu____686))
end))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end)))));
)
end
| uu____698 -> begin
(

let uu____699 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (uu____699) with
| (univ_vars, t) -> begin
((univ_vars), (t), (false))
end))
end)))
end))


let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c))) None p.FStar_Syntax_Syntax.p)
in (([]), ([]), ([]), (env), (e), (p)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____782) -> begin
(

let uu____787 = (FStar_Syntax_Util.type_u ())
in (match (uu____787) with
| (k, uu____800) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let uu___112_803 = x
in {FStar_Syntax_Syntax.ppname = uu___112_803.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_803.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____804 = (

let uu____807 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p uu____807 t))
in (match (uu____804) with
| (e, u) -> begin
(

let p = (

let uu___113_822 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = uu___113_822.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___113_822.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____829 = (FStar_Syntax_Util.type_u ())
in (match (uu____829) with
| (t, uu____842) -> begin
(

let x = (

let uu___114_844 = x
in (

let uu____845 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = uu___114_844.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_844.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____845}))
in (

let env = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env x)
end
| uu____849 -> begin
env
end)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x))) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ([]), ((x)::[]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____867 = (FStar_Syntax_Util.type_u ())
in (match (uu____867) with
| (t, uu____880) -> begin
(

let x = (

let uu___115_882 = x
in (

let uu____883 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = uu___115_882.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_882.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____883}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x))) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____915 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____971 uu____972 -> (match (((uu____971), (uu____972))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let uu____1071 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (uu____1071) with
| (b', a', w', env, te, pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1110 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (((b')::b), ((a')::a), ((w')::w), (env), ((arg)::args), ((((pat), (imp)))::pats)))
end))
end)) (([]), ([]), ([]), (env), ([]), ([]))))
in (match (uu____915) with
| (b, a, w, env, args, pats) -> begin
(

let e = (

let uu____1179 = (

let uu____1182 = (

let uu____1183 = (

let uu____1188 = (

let uu____1191 = (

let uu____1192 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____1193 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____1192 uu____1193)))
in (uu____1191 None p.FStar_Syntax_Syntax.p))
in ((uu____1188), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____1183))
in (FStar_Syntax_Syntax.mk uu____1182))
in (uu____1179 None p.FStar_Syntax_Syntax.p))
in (

let uu____1210 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____1216 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____1222 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____1210), (uu____1216), (uu____1222), (env), (e), ((

let uu___116_1235 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___116_1235.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___116_1235.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (uu____1241) -> begin
(failwith "impossible")
end))
in (

let rec elaborate_pat = (fun env p -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end
| uu____1281 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats = (FStar_List.map (fun uu____1310 -> (match (uu____1310) with
| (p, imp) -> begin
(

let uu____1325 = (elaborate_pat env p)
in ((uu____1325), (imp)))
end)) pats)
in (

let uu____1330 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1330) with
| (uu____1339, t) -> begin
(

let uu____1341 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____1341) with
| (f, uu____1352) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (uu____1427)::uu____1428) -> begin
(Prims.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((uu____1463)::uu____1464, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____1504 -> (match (uu____1504) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____1522 = (

let uu____1524 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (uu____1524))
in (FStar_Syntax_Syntax.new_bv uu____1522 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____1530 = (maybe_dot inaccessible a r)
in ((uu____1530), (true)))))
end
| uu____1535 -> begin
(

let uu____1537 = (

let uu____1538 = (

let uu____1541 = (

let uu____1542 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____1542))
in ((uu____1541), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Errors.Error (uu____1538))
in (Prims.raise uu____1537))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (uu____1593, Some (FStar_Syntax_Syntax.Implicit (uu____1594))) when p_imp -> begin
(

let uu____1596 = (aux formals' pats')
in (((p), (true)))::uu____1596)
end
| (uu____1608, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (

let uu____1619 = (aux formals' pats)
in (((p), (true)))::uu____1619)))
end
| (uu____1631, imp) -> begin
(

let uu____1635 = (

let uu____1640 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (uu____1640)))
in (

let uu____1643 = (aux formals' pats')
in (uu____1635)::uu____1643))
end)
end))
in (

let uu___117_1653 = p
in (

let uu____1656 = (

let uu____1657 = (

let uu____1665 = (aux f pats)
in ((fv), (uu____1665)))
in FStar_Syntax_Syntax.Pat_cons (uu____1657))
in {FStar_Syntax_Syntax.v = uu____1656; FStar_Syntax_Syntax.ty = uu___117_1653.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___117_1653.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____1676 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let uu____1702 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (uu____1702) with
| (b, a, w, env, arg, p) -> begin
(

let uu____1732 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____1732) with
| Some (x) -> begin
(

let uu____1745 = (

let uu____1746 = (

let uu____1749 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in ((uu____1749), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____1746))
in (Prims.raise uu____1745))
end
| uu____1758 -> begin
((b), (a), (w), (arg), (p))
end))
end))))
in (

let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((q)::pats) -> begin
(

let uu____1801 = (one_pat false env q)
in (match (uu____1801) with
| (b, a, uu____1817, te, q) -> begin
(

let uu____1826 = (FStar_List.fold_right (fun p uu____1842 -> (match (uu____1842) with
| (w, args, pats) -> begin
(

let uu____1866 = (one_pat false env p)
in (match (uu____1866) with
| (b', a', w', arg, p) -> begin
(

let uu____1892 = (

let uu____1893 = (FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a')
in (not (uu____1893)))
in (match (uu____1892) with
| true -> begin
(

let uu____1900 = (

let uu____1901 = (

let uu____1904 = (FStar_TypeChecker_Err.disjunctive_pattern_vars a a')
in (

let uu____1905 = (FStar_TypeChecker_Env.get_range env)
in ((uu____1904), (uu____1905))))
in FStar_Errors.Error (uu____1901))
in (Prims.raise uu____1900))
end
| uu____1912 -> begin
(

let uu____1913 = (

let uu____1915 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____1915)::args)
in (((FStar_List.append w' w)), (uu____1913), ((p)::pats)))
end))
end))
end)) pats (([]), ([]), ([])))
in (match (uu____1826) with
| (w, args, pats) -> begin
(

let uu____1936 = (

let uu____1938 = (FStar_Syntax_Syntax.as_arg te)
in (uu____1938)::args)
in (((FStar_List.append b w)), (uu____1936), ((

let uu___118_1943 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = uu___118_1943.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___118_1943.FStar_Syntax_Syntax.p}))))
end))
end))
end
| uu____1944 -> begin
(

let uu____1945 = (one_pat true env p)
in (match (uu____1945) with
| (b, uu____1960, uu____1961, arg, p) -> begin
(

let uu____1970 = (

let uu____1972 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____1972)::[])
in ((b), (uu____1970), (p)))
end))
end))
in (

let uu____1975 = (top_level_pat_as_args env p)
in (match (uu____1975) with
| (b, args, p) -> begin
(

let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in ((b), (exps), (p)))
end)))))))


let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (

let qq = p
in (

let rec aux = (fun p e -> (

let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (

let e = (FStar_Syntax_Util.unmeta e)
in (match (((p.FStar_Syntax_Syntax.v), (e.FStar_Syntax_Syntax.n))) with
| (uu____2046, FStar_Syntax_Syntax.Tm_uinst (e, uu____2048)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____2053), FStar_Syntax_Syntax.Tm_constant (uu____2054)) -> begin
(

let uu____2055 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v uu____2055))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____2059 = (

let uu____2060 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2061 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2060 uu____2061)))
in (failwith uu____2059))
end
| uu____2062 -> begin
()
end);
(

let uu____2064 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____2064) with
| true -> begin
(

let uu____2065 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2066 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____2065 uu____2066)))
end
| uu____2067 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___119_2070 = x
in {FStar_Syntax_Syntax.ppname = uu___119_2070.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_2070.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____2074 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____2074) with
| true -> begin
(

let uu____2075 = (

let uu____2076 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2077 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____2076 uu____2077)))
in (failwith uu____2075))
end
| uu____2078 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let uu___120_2081 = x
in {FStar_Syntax_Syntax.ppname = uu___120_2081.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___120_2081.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n)));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____2083), uu____2084) -> begin
(

let s = (force_sort e)
in (

let x = (

let uu___121_2093 = x
in {FStar_Syntax_Syntax.ppname = uu___121_2093.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___121_2093.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____2106 = (

let uu____2107 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____2107)))
in (match (uu____2106) with
| true -> begin
(

let uu____2108 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2108))
end
| uu____2117 -> begin
()
end));
(

let uu____2118 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) uu____2118));
)
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
((

let uu____2189 = (

let uu____2190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____2190 Prims.op_Negation))
in (match (uu____2189) with
| true -> begin
(

let uu____2191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____2191))
end
| uu____2200 -> begin
()
end));
(

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(

let uu____2279 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) uu____2279))
end
| ((arg)::args, ((argpat, uu____2292))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____2342)) -> begin
(

let x = (

let uu____2358 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) uu____2358))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), uu____2372) -> begin
(

let pat = (

let uu____2387 = (aux argpat e)
in (

let uu____2388 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____2387), (uu____2388))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| uu____2391 -> begin
(

let uu____2405 = (

let uu____2406 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____2407 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____2406 uu____2407)))
in (failwith uu____2405))
end))
in (match_args [] args argpats)));
)
end
| uu____2414 -> begin
(

let uu____2417 = (

let uu____2418 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____2419 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____2420 = (

let uu____2421 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right uu____2421 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____2418 uu____2419 uu____2420))))
in (failwith uu____2417))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), uu____2428) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (uu____2444, (e)::[]) -> begin
(aux p e)
end
| uu____2447 -> begin
(failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> ((FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____2486 -> (match (uu____2486) with
| (p, i) -> begin
(

let uu____2496 = (decorated_pattern_as_term p)
in (match (uu____2496) with
| (vars, te) -> begin
(

let uu____2509 = (

let uu____2512 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____2512)))
in ((vars), (uu____2509)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____2519) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____2527 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____2527)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(

let uu____2534 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____2534)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____2552 = (

let uu____2560 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____2560 FStar_List.unzip))
in (match (uu____2552) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (

let uu____2618 = (

let uu____2621 = (

let uu____2622 = (

let uu____2632 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____2632), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____2622))
in (mk uu____2621))
in ((vars), (uu____2618))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____2663))::[] -> begin
wp
end
| uu____2676 -> begin
(

let uu____2682 = (

let uu____2683 = (

let uu____2684 = (FStar_List.map (fun uu____2688 -> (match (uu____2688) with
| (x, uu____2692) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____2684 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____2683))
in (failwith uu____2682))
end)
in (

let uu____2696 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____2696), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____2724 = (destruct_comp c)
in (match (uu____2724) with
| (u, uu____2729, wp) -> begin
(

let uu____2731 = (

let uu____2737 = (

let uu____2738 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____2738))
in (uu____2737)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____2731; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____2748 = (

let uu____2752 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____2753 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____2752 uu____2753)))
in (match (uu____2748) with
| (m, uu____2755, uu____2756) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____2766 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____2766) with
| true -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| uu____2767 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (

let uu____2791 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (uu____2791) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____2821 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____2821) with
| (a, kwp) -> begin
(

let uu____2838 = (destruct_comp m1)
in (

let uu____2842 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____2838), (uu____2842))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (

let uu____2890 = (

let uu____2891 = (

let uu____2897 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2897)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____2891; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp uu____2890)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (match ((FStar_Ident.lid_equals mname FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (Some (u_result)))
end
| uu____2926 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let uu___122_2933 = lc
in (

let uu____2934 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___122_2933.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____2934; FStar_Syntax_Syntax.cflags = uu___122_2933.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2937 -> (

let uu____2938 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst uu____2938)))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2942 = (

let uu____2943 = (FStar_Syntax_Subst.compress t)
in uu____2943.FStar_Syntax_Syntax.n)
in (match (uu____2942) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2946) -> begin
true
end
| uu____2954 -> begin
false
end)))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = (

let uu____2965 = (

let uu____2966 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____2966))
in (match (uu____2965) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____2967 -> begin
(

let m = (

let uu____2969 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must uu____2969))
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (

let uu____2973 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2973) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____2974 -> begin
(

let uu____2975 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (uu____2975) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____2981 = (

let uu____2982 = (

let uu____2983 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2984 = (

let uu____2985 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____2986 = (

let uu____2988 = (FStar_Syntax_Syntax.as_arg v)
in (uu____2988)::[])
in (uu____2985)::uu____2986))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2983 uu____2984)))
in (uu____2982 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env uu____2981)))
end))
end))
in ((mk_comp m) u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
in ((

let uu____2994 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____2994) with
| true -> begin
(

let uu____2995 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (

let uu____2996 = (FStar_Syntax_Print.term_to_string v)
in (

let uu____2997 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2995 uu____2996 uu____2997))))
end
| uu____2998 -> begin
()
end));
c;
)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____3014 -> (match (uu____3014) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc1 lc2)
in ((

let uu____3024 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____3024) with
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

let uu____3027 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (

let uu____3029 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (

let uu____3030 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" uu____3027 uu____3029 bstr uu____3030)))))
end
| uu____3031 -> begin
()
end));
(

let bind_it = (fun uu____3035 -> (

let uu____3036 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3036) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc2.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc2.FStar_Syntax_Syntax.res_typ []))
end
| uu____3038 -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in ((

let uu____3046 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____3046) with
| true -> begin
(

let uu____3047 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____3049 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (

let uu____3050 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____3051 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (

let uu____3052 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" uu____3047 uu____3049 uu____3050 uu____3051 uu____3052))))))
end
| uu____3053 -> begin
()
end));
(

let try_simplify = (fun uu____3060 -> (

let aux = (fun uu____3069 -> (

let uu____3070 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____3070) with
| true -> begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (uu____3087) -> begin
(

let uu____3088 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____3088) with
| true -> begin
Some (((c2), ("trivial ml")))
end
| uu____3100 -> begin
None
end))
end)
end
| uu____3105 -> begin
(

let uu____3106 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____3106) with
| true -> begin
Some (((c2), ("both ml")))
end
| uu____3118 -> begin
None
end))
end)))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
(

let uu____3139 = (

let uu____3142 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____3142), (reason)))
in Some (uu____3139))
end
| uu____3145 -> begin
(aux ())
end))
in (

let uu____3150 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____3150) with
| true -> begin
(subst_c2 "both total")
end
| uu____3154 -> begin
(

let uu____3155 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3155) with
| true -> begin
(

let uu____3159 = (

let uu____3162 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____3162), ("both gtot")))
in Some (uu____3159))
end
| uu____3165 -> begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
(

let uu____3175 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____3176 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____3176))))
in (match (uu____3175) with
| true -> begin
(subst_c2 "substituted e")
end
| uu____3180 -> begin
(aux ())
end))
end
| uu____3181 -> begin
(aux ())
end)
end))
end)))))
in (

let uu____3186 = (try_simplify ())
in (match (uu____3186) with
| Some (c, reason) -> begin
c
end
| None -> begin
(

let uu____3196 = (lift_and_destruct env c1 c2)
in (match (uu____3196) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(

let uu____3230 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____3230)::[])
end
| Some (x) -> begin
(

let uu____3232 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3232)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)))) None r1)
in (

let wp_args = (

let uu____3259 = (FStar_Syntax_Syntax.as_arg r1)
in (

let uu____3260 = (

let uu____3262 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3263 = (

let uu____3265 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____3266 = (

let uu____3268 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____3269 = (

let uu____3271 = (

let uu____3272 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____3272))
in (uu____3271)::[])
in (uu____3268)::uu____3269))
in (uu____3265)::uu____3266))
in (uu____3262)::uu____3263))
in (uu____3259)::uu____3260))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (

let uu____3277 = (

let uu____3278 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3278 wp_args))
in (uu____3277 None t2.FStar_Syntax_Syntax.pos))
in (

let c = ((mk_comp md) u_t2 t2 wp [])
in c)))))))
end))
end)));
)))
end)))
in {FStar_Syntax_Syntax.eff_name = joined_eff; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it});
))))
end))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false)))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
(

let uu____3327 = (

let uu____3328 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____3328))
in (match (uu____3327) with
| true -> begin
f
end
| uu____3329 -> begin
(

let uu____3330 = (reason ())
in (label uu____3330 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___123_3341 = g
in (

let uu____3342 = (

let uu____3343 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____3343))
in {FStar_TypeChecker_Env.guard_f = uu____3342; FStar_TypeChecker_Env.deferred = uu___123_3341.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___123_3341.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___123_3341.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____3353 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____3370 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3374 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3374) with
| true -> begin
c
end
| uu____3377 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____3381 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3381) with
| true -> begin
c
end
| uu____3384 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3386 = (destruct_comp c)
in (match (uu____3386) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (

let uu____3399 = (

let uu____3400 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____3401 = (

let uu____3402 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3403 = (

let uu____3405 = (FStar_Syntax_Syntax.as_arg f)
in (

let uu____3406 = (

let uu____3408 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3408)::[])
in (uu____3405)::uu____3406))
in (uu____3402)::uu____3403))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3400 uu____3401)))
in (uu____3399 None wp.FStar_Syntax_Syntax.pos))
in ((mk_comp md) u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end))
end)
end))))
in (

let uu___124_3413 = lc
in {FStar_Syntax_Syntax.eff_name = uu___124_3413.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___124_3413.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___124_3413.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> (

let uu____3440 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____3440) with
| true -> begin
((lc), (g0))
end
| uu____3443 -> begin
((

let uu____3445 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3445) with
| true -> begin
(

let uu____3446 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____3447 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" uu____3446 uu____3447)))
end
| uu____3448 -> begin
()
end));
(

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___91_3453 -> (match (uu___91_3453) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| uu____3455 -> begin
[]
end))))
in (

let strengthen = (fun uu____3461 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____3467 -> begin
(

let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____3469 = (FStar_TypeChecker_Rel.guard_form g0)
in (match (uu____3469) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c = (

let uu____3476 = ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (

let uu____3477 = (FStar_Syntax_Util.is_partial_return c)
in (not (uu____3477))))
in (match (uu____3476) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (

let xret = (

let uu____3484 = (

let uu____3485 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort uu____3485))
in (FStar_Syntax_Util.comp_set_flags uu____3484 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end
| uu____3488 -> begin
c
end))
in ((

let uu____3490 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3490) with
| true -> begin
(

let uu____3491 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (

let uu____3492 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____3491 uu____3492)))
end
| uu____3493 -> begin
()
end));
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____3495 = (destruct_comp c)
in (match (uu____3495) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (

let uu____3508 = (

let uu____3509 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____3510 = (

let uu____3511 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3512 = (

let uu____3514 = (

let uu____3515 = (

let uu____3516 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____3516 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3515))
in (

let uu____3517 = (

let uu____3519 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3519)::[])
in (uu____3514)::uu____3517))
in (uu____3511)::uu____3512))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3509 uu____3510)))
in (uu____3508 None wp.FStar_Syntax_Syntax.pos))
in ((

let uu____3525 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____3525) with
| true -> begin
(

let uu____3526 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" uu____3526))
end
| uu____3527 -> begin
()
end));
(

let c2 = ((mk_comp md) u_res_t res_t wp flags)
in c2);
)))
end)));
))
end)))
end)))
in (

let uu____3529 = (

let uu___125_3530 = lc
in (

let uu____3531 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____3532 = (

let uu____3534 = ((FStar_Syntax_Util.is_pure_lcomp lc) && (

let uu____3535 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation uu____3535)))
in (match (uu____3534) with
| true -> begin
flags
end
| uu____3537 -> begin
[]
end))
in {FStar_Syntax_Syntax.eff_name = uu____3531; FStar_Syntax_Syntax.res_typ = uu___125_3530.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu____3532; FStar_Syntax_Syntax.comp = strengthen})))
in ((uu____3529), ((

let uu___126_3538 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___126_3538.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___126_3538.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___126_3538.FStar_TypeChecker_Env.implicits}))))));
)
end)))


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let uu____3553 = (

let uu____3556 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____3557 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____3556), (uu____3557))))
in (match (uu____3553) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (

let uu____3566 = (

let uu____3567 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (

let uu____3568 = (

let uu____3569 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3570 = (

let uu____3572 = (FStar_Syntax_Syntax.as_arg yexp)
in (uu____3572)::[])
in (uu____3569)::uu____3570))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3567 uu____3568)))
in (uu____3566 None res_t.FStar_Syntax_Syntax.pos))
in (

let x_eq_y_yret = (

let uu____3580 = (

let uu____3581 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (

let uu____3582 = (

let uu____3583 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3584 = (

let uu____3586 = (

let uu____3587 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3587))
in (

let uu____3588 = (

let uu____3590 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (uu____3590)::[])
in (uu____3586)::uu____3588))
in (uu____3583)::uu____3584))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3581 uu____3582)))
in (uu____3580 None res_t.FStar_Syntax_Syntax.pos))
in (

let forall_y_x_eq_y_yret = (

let uu____3598 = (

let uu____3599 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (

let uu____3600 = (

let uu____3601 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3602 = (

let uu____3604 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3605 = (

let uu____3607 = (

let uu____3608 = (

let uu____3609 = (

let uu____3613 = (FStar_Syntax_Syntax.mk_binder y)
in (uu____3613)::[])
in (FStar_Syntax_Util.abs uu____3609 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3608))
in (uu____3607)::[])
in (uu____3604)::uu____3605))
in (uu____3601)::uu____3602))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3599 uu____3600)))
in (uu____3598 None res_t.FStar_Syntax_Syntax.pos))
in (

let lc2 = ((mk_comp md_pure) u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (

let uu____3629 = (FStar_TypeChecker_Env.get_range env)
in (bind uu____3629 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun uu____3647 -> (

let uu____3648 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3648) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end
| uu____3650 -> begin
(

let uu____3651 = (

let uu____3664 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (

let uu____3665 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____3664 uu____3665)))
in (match (uu____3651) with
| ((md, uu____3667, uu____3668), (u_res_t, res_t, wp_then), (uu____3672, uu____3673, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (

let uu____3702 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____3703 = (

let uu____3704 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3705 = (

let uu____3706 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3707 = (

let uu____3709 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____3710 = (

let uu____3712 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____3713 = (

let uu____3715 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____3715)::[])
in (uu____3712)::uu____3713))
in (uu____3709)::uu____3710))
in (uu____3706)::uu____3707))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3704 uu____3705)))
in (uu____3703 None uu____3702))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let uu____3723 = (

let uu____3724 = (FStar_Options.split_cases ())
in (uu____3724 > (Prims.parse_int "0")))
in (match (uu____3723) with
| true -> begin
(

let comp = ((mk_comp md) u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end
| uu____3726 -> begin
(

let wp = (

let uu____3730 = (

let uu____3731 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____3732 = (

let uu____3733 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3734 = (

let uu____3736 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3736)::[])
in (uu____3733)::uu____3734))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3731 uu____3732)))
in (uu____3730 None wp.FStar_Syntax_Syntax.pos))
in ((mk_comp md) u_res_t res_t wp []))
end))))
end))
end)))
in (

let uu____3741 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____3741; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____3748 = (

let uu____3749 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____3749))
in (FStar_Syntax_Syntax.fvar uu____3748 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____3769 -> (match (uu____3769) with
| (uu____3772, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun uu____3777 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____3779 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3779) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____3780 -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (

let uu____3799 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____3800 = (

let uu____3801 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3802 = (

let uu____3803 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3804 = (

let uu____3806 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____3807 = (

let uu____3809 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____3810 = (

let uu____3812 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____3812)::[])
in (uu____3809)::uu____3810))
in (uu____3806)::uu____3807))
in (uu____3803)::uu____3804))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3801 uu____3802)))
in (uu____3800 None uu____3799))))
in (

let default_case = (

let post_k = (

let uu____3821 = (

let uu____3825 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____3825)::[])
in (

let uu____3826 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3821 uu____3826)))
in (

let kwp = (

let uu____3832 = (

let uu____3836 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____3836)::[])
in (

let uu____3837 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3832 uu____3837)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (

let uu____3842 = (

let uu____3846 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____3846)::[])
in (

let uu____3847 = (

let uu____3848 = (

let uu____3851 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____3851))
in (

let uu____3852 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left uu____3848 uu____3852)))
in (FStar_Syntax_Util.abs uu____3842 uu____3847 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in ((mk_comp md) u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun uu____3866 celse -> (match (uu____3866) with
| (g, cthen) -> begin
(

let uu____3872 = (

let uu____3885 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env uu____3885 celse))
in (match (uu____3872) with
| ((md, uu____3887, uu____3888), (uu____3889, uu____3890, wp_then), (uu____3892, uu____3893, wp_else)) -> begin
(

let uu____3904 = (ifthenelse md res_t g wp_then wp_else)
in ((mk_comp md) u_res_t res_t uu____3904 []))
end))
end)) lcases default_case)
in (

let uu____3905 = (

let uu____3906 = (FStar_Options.split_cases ())
in (uu____3906 > (Prims.parse_int "0")))
in (match (uu____3905) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| uu____3907 -> begin
(

let comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____3910 = (destruct_comp comp)
in (match (uu____3910) with
| (uu____3914, uu____3915, wp) -> begin
(

let wp = (

let uu____3920 = (

let uu____3921 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____3922 = (

let uu____3923 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____3924 = (

let uu____3926 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3926)::[])
in (uu____3923)::uu____3924))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3921 uu____3922)))
in (uu____3920 None wp.FStar_Syntax_Syntax.pos))
in ((mk_comp md) u_res_t res_t wp []))
end))))
end)))))
end))))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun uu____3947 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____3951 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____3951) with
| true -> begin
c
end
| uu____3954 -> begin
(

let uu____3955 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3955) with
| true -> begin
c
end
| uu____3958 -> begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____3987 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3987)::[])
in (

let us = (

let uu____3990 = (

let uu____3992 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____3992)::[])
in (u_res)::uu____3990)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let uu____4003 = (

let uu____4004 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____4005 = (

let uu____4006 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4007 = (

let uu____4009 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____4010 = (

let uu____4012 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4012)::[])
in (uu____4009)::uu____4010))
in (uu____4006)::uu____4007))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4004 uu____4005)))
in (uu____4003 None wp0.FStar_Syntax_Syntax.pos)))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____4018 = (destruct_comp c)
in (match (uu____4018) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (close_wp u_res_t md res_t bvs wp)
in ((mk_comp md) u_res_t c.FStar_Syntax_Syntax.result_typ wp c.FStar_Syntax_Syntax.flags)))
end))))
end))
end))))
in (

let uu___127_4029 = lc
in {FStar_Syntax_Syntax.eff_name = uu___127_4029.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___127_4029.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___127_4029.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun uu____4044 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let uu____4048 = ((

let uu____4049 = (is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name)
in (not (uu____4049))) || env.FStar_TypeChecker_Env.lax)
in (match (uu____4048) with
| true -> begin
c
end
| uu____4052 -> begin
(

let uu____4053 = (FStar_Syntax_Util.is_partial_return c)
in (match (uu____4053) with
| true -> begin
c
end
| uu____4056 -> begin
(

let uu____4057 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (

let uu____4058 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (not (uu____4058))))
in (match (uu____4057) with
| true -> begin
(

let uu____4061 = (

let uu____4062 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____4063 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" uu____4062 uu____4063)))
in (failwith uu____4061))
end
| uu____4066 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let t = c.FStar_Syntax_Syntax.result_typ
in (

let c = (FStar_Syntax_Syntax.mk_Comp c)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let ret = (

let uu____4075 = (

let uu____4078 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____4078 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4075))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (

let uu____4092 = (

let uu____4093 = (

let uu____4098 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in uu____4098.FStar_Syntax_Syntax.comp)
in (uu____4093 ()))
in (FStar_Syntax_Util.comp_set_flags uu____4092 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end))
end))
end))))
in (

let flags = (

let uu____4102 = (((

let uu____4103 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____4103))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (

let uu____4104 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____4104))))
in (match (uu____4102) with
| true -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____4106 -> begin
lc.FStar_Syntax_Syntax.cflags
end))
in (

let uu___128_4107 = lc
in {FStar_Syntax_Syntax.eff_name = uu___128_4107.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___128_4107.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____4126 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____4126) with
| None -> begin
(

let uu____4131 = (

let uu____4132 = (

let uu____4135 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____4136 = (FStar_TypeChecker_Env.get_range env)
in ((uu____4135), (uu____4136))))
in FStar_Errors.Error (uu____4132))
in (Prims.raise uu____4131))
end
| Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let uu____4157 = (

let uu____4158 = (FStar_Syntax_Subst.compress t)
in uu____4158.FStar_Syntax_Syntax.n)
in (match (uu____4157) with
| FStar_Syntax_Syntax.Tm_type (uu____4163) -> begin
(

let uu____4164 = (

let uu____4165 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in uu____4165.FStar_Syntax_Syntax.n)
in (match (uu____4164) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let uu____4171 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc = (

let uu____4176 = (

let uu____4177 = (

let uu____4178 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4178))
in ((None), (uu____4177)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc uu____4176))
in (

let e = (

let uu____4187 = (

let uu____4188 = (

let uu____4189 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4189)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t uu____4188))
in (uu____4187 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e), (lc))))))
end
| uu____4196 -> begin
((e), (lc))
end))
end
| uu____4197 -> begin
((e), (lc))
end)))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(

let uu____4223 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4223), (false)))
end
| uu____4226 -> begin
(

let uu____4227 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4227), (true)))
end)
in (match (gopt) with
| (None, uu____4233) -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___129_4236 = lc
in {FStar_Syntax_Syntax.eff_name = uu___129_4236.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___129_4236.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___129_4236.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard));
)
end
| (Some (g), apply_guard) -> begin
(

let uu____4240 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____4240) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let uu___130_4245 = lc
in {FStar_Syntax_Syntax.eff_name = uu___130_4245.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___130_4245.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___130_4245.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let uu___131_4248 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___131_4248.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___131_4248.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___131_4248.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____4254 -> (

let uu____4255 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4255) with
| true -> begin
(lc.FStar_Syntax_Syntax.comp ())
end
| uu____4258 -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let uu____4260 = (

let uu____4261 = (FStar_Syntax_Subst.compress f)
in uu____4261.FStar_Syntax_Syntax.n)
in (match (uu____4260) with
| FStar_Syntax_Syntax.Tm_abs (uu____4266, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____4268; FStar_Syntax_Syntax.pos = uu____4269; FStar_Syntax_Syntax.vars = uu____4270}, uu____4271) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let uu___132_4295 = lc
in {FStar_Syntax_Syntax.eff_name = uu___132_4295.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___132_4295.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___132_4295.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| uu____4296 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in ((

let uu____4301 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4301) with
| true -> begin
(

let uu____4302 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____4303 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____4304 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____4305 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____4302 uu____4303 uu____4304 uu____4305)))))
end
| uu____4306 -> begin
()
end));
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____4308 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (uu____4308) with
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

let uu____4319 = (destruct_comp ct)
in (match (uu____4319) with
| (u_t, uu____4326, uu____4327) -> begin
(

let wp = (

let uu____4331 = (

let uu____4332 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (

let uu____4333 = (

let uu____4334 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____4335 = (

let uu____4337 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____4337)::[])
in (uu____4334)::uu____4335))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4332 uu____4333)))
in (uu____4331 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos))
in (

let cret = (

let uu____4343 = ((mk_comp md) u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4343))
in (

let guard = (match (apply_guard) with
| true -> begin
(

let uu____4353 = (

let uu____4354 = (

let uu____4355 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____4355)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f uu____4354))
in (uu____4353 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end
| uu____4360 -> begin
f
end)
in (

let uu____4361 = (

let uu____4364 = (FStar_All.pipe_left (fun _0_28 -> Some (_0_28)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____4375 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____4376 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____4364 uu____4375 e cret uu____4376))))
in (match (uu____4361) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let uu___133_4382 = x
in {FStar_Syntax_Syntax.ppname = uu___133_4382.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_4382.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (

let uu____4384 = (

let uu____4385 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4385))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) uu____4384 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in ((

let uu____4395 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4395) with
| true -> begin
(

let uu____4396 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" uu____4396))
end
| uu____4397 -> begin
()
end));
c;
))))
end)))))
end))))))
end)));
))
end)))
end)))
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___92_4402 -> (match (uu___92_4402) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____4404 -> begin
[]
end))))
in (

let lc = (

let uu___134_4406 = lc
in (

let uu____4407 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = uu____4407; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let uu___135_4409 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___135_4409.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___135_4409.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___135_4409.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end))
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let uu____4429 = (

let uu____4430 = (

let uu____4431 = (

let uu____4432 = (

let uu____4433 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____4433))
in (uu____4432)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____4431))
in (uu____4430 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____4429))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____4442 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____4442) with
| true -> begin
((None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____4449 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (_)) | (FStar_Syntax_Syntax.Total (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(match (((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____4466))::((ens, uu____4468))::uu____4469 -> begin
(

let uu____4491 = (

let uu____4493 = (norm req)
in Some (uu____4493))
in (

let uu____4494 = (

let uu____4495 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm uu____4495))
in ((uu____4491), (uu____4494))))
end
| uu____4497 -> begin
(

let uu____4503 = (

let uu____4504 = (

let uu____4507 = (

let uu____4508 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____4508))
in ((uu____4507), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____4504))
in (Prims.raise uu____4503))
end)
end
| uu____4512 -> begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____4518))::uu____4519 -> begin
(

let uu____4533 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (uu____4533) with
| (us_r, uu____4540) -> begin
(

let uu____4541 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (uu____4541) with
| (us_e, uu____4548) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____4551 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4551 us_r))
in (

let as_ens = (

let uu____4553 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4553 us_e))
in (

let req = (

let uu____4557 = (

let uu____4558 = (

let uu____4559 = (

let uu____4566 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4566)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::uu____4559)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____4558))
in (uu____4557 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____4582 = (

let uu____4583 = (

let uu____4584 = (

let uu____4591 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4591)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::uu____4584)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____4583))
in (uu____4582 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____4604 = (

let uu____4606 = (norm req)
in Some (uu____4606))
in (

let uu____4607 = (

let uu____4608 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm uu____4608))
in ((uu____4604), (uu____4607)))))))))
end))
end))
end
| uu____4610 -> begin
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
| uu____4635 -> begin
(

let number_of_implicits = (fun t -> (

let uu____4640 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____4640) with
| (formals, uu____4649) -> begin
(

let n_implicits = (

let uu____4661 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____4698 -> (match (uu____4698) with
| (uu____4702, imp) -> begin
((imp = None) || (imp = Some (FStar_Syntax_Syntax.Equality)))
end))))
in (match (uu____4661) with
| None -> begin
(FStar_List.length formals)
end
| Some (implicits, _first_explicit, _rest) -> begin
(FStar_List.length implicits)
end))
in n_implicits)
end)))
in (

let inst_n_binders = (fun t -> (

let uu____4774 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____4774) with
| None -> begin
None
end
| Some (expected_t) -> begin
(

let n_expected = (number_of_implicits expected_t)
in (

let n_available = (number_of_implicits t)
in (match ((n_available < n_expected)) with
| true -> begin
(

let uu____4788 = (

let uu____4789 = (

let uu____4792 = (

let uu____4793 = (FStar_Util.string_of_int n_expected)
in (

let uu____4797 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____4798 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____4793 uu____4797 uu____4798))))
in (

let uu____4802 = (FStar_TypeChecker_Env.get_range env)
in ((uu____4792), (uu____4802))))
in FStar_Errors.Error (uu____4789))
in (Prims.raise uu____4788))
end
| uu____4804 -> begin
Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___93_4815 -> (match (uu___93_4815) with
| None -> begin
None
end
| Some (i) -> begin
Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4834 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4834) with
| (bs, c) -> begin
(

let rec aux = (fun subst inst_n bs -> (match (((inst_n), (bs))) with
| (Some (_0_29), uu____4895) when (_0_29 = (Prims.parse_int "0")) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____4917, ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let uu____4936 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (uu____4936) with
| (v, uu____4957, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let uu____4967 = (aux subst (decr_inst inst_n) rest)
in (match (uu____4967) with
| (args, bs, subst, g') -> begin
(

let uu____5016 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (uu____5016)))
end)))
end)))
end
| (uu____5030, bs) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____5054 = (

let uu____5068 = (inst_n_binders t)
in (aux [] uu____5068 bs))
in (match (uu____5054) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], uu____5106) -> begin
((e), (torig), (guard))
end
| (uu____5122, []) when (

let uu____5138 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____5138))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____5139 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____5158 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let e = ((FStar_Syntax_Syntax.mk_Tm_app e args) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((e), (t), (guard)))))
end)
end)))
end))
end
| uu____5173 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs = (fun univs -> (

let uu____5185 = (

let uu____5187 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right uu____5187 (FStar_List.map (fun u -> (

let uu____5197 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____5197 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____5185 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____5209 = (FStar_Util.set_is_empty x)
in (match (uu____5209) with
| true -> begin
[]
end
| uu____5211 -> begin
(

let s = (

let uu____5214 = (

let uu____5216 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____5216))
in (FStar_All.pipe_right uu____5214 FStar_Util.set_elements))
in ((

let uu____5221 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5221) with
| true -> begin
(

let uu____5222 = (

let uu____5223 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____5223))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____5222))
end
| uu____5228 -> begin
()
end));
(

let r = (

let uu____5231 = (FStar_TypeChecker_Env.get_range env)
in Some (uu____5231))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____5243 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5243) with
| true -> begin
(

let uu____5244 = (

let uu____5245 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____5245))
in (

let uu____5247 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____5248 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____5244 uu____5247 uu____5248))))
end
| uu____5249 -> begin
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

let univnames = (

let uu____5266 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____5266 FStar_Util.fifo_set_elements))
in univnames))))


let maybe_set_tk = (fun ts uu___94_5293 -> (match (uu___94_5293) with
| None -> begin
ts
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange)
in (

let t = (FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t)
in ((FStar_ST.write (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)));
ts;
)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____5334) -> begin
generalized_univ_names
end
| (uu____5338, []) -> begin
explicit_univ_names
end
| uu____5342 -> begin
(

let uu____5347 = (

let uu____5348 = (

let uu____5351 = (

let uu____5352 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____5352))
in ((uu____5351), (t.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____5348))
in (Prims.raise uu____5347))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames = (gather_free_univnames env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in ((

let uu____5366 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5366) with
| true -> begin
(

let uu____5367 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" uu____5367))
end
| uu____5369 -> begin
()
end));
(

let gen = (gen_univs env univs)
in ((

let uu____5373 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____5373) with
| true -> begin
(

let uu____5374 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" uu____5374))
end
| uu____5375 -> begin
()
end));
(

let univs = (check_universe_generalization univnames gen t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs t)
in (

let uu____5379 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs), (ts)) uu____5379))));
));
)))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> (

let uu____5409 = (

let uu____5410 = (FStar_Util.for_all (fun uu____5415 -> (match (uu____5415) with
| (uu____5420, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation uu____5410))
in (match (uu____5409) with
| true -> begin
None
end
| uu____5437 -> begin
(

let norm = (fun c -> ((

let uu____5443 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5443) with
| true -> begin
(

let uu____5444 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____5444))
end
| uu____5445 -> begin
()
end));
(

let c = (

let uu____5447 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____5447) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
| uu____5448 -> begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end))
in ((

let uu____5450 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5450) with
| true -> begin
(

let uu____5451 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5451))
end
| uu____5452 -> begin
()
end));
c;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____5485 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____5485 FStar_Util.set_elements)))
in (

let uu____5529 = (

let uu____5547 = (FStar_All.pipe_right ecs (FStar_List.map (fun uu____5602 -> (match (uu____5602) with
| (e, c) -> begin
(

let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (

let c = (norm c)
in (

let t = (FStar_Syntax_Util.comp_result c)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let uvt = (FStar_Syntax_Free.uvars t)
in (

let uvs = (gen_uvars uvt)
in ((univs), (((uvs), (e), (c))))))))))
end))))
in (FStar_All.pipe_right uu____5547 FStar_List.unzip))
in (match (uu____5529) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in ((

let uu____5764 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____5764) with
| true -> begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end
| uu____5767 -> begin
()
end));
(

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun uu____5806 -> (match (uu____5806) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun uu____5863 -> (match (uu____5863) with
| (u, k) -> begin
(

let uu____5883 = (FStar_Unionfind.find u)
in (match (uu____5883) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (uu____5921) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____5929 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let uu____5934 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____5934) with
| (bs, kres) -> begin
(

let a = (

let uu____5958 = (

let uu____5960 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____5960))
in (FStar_Syntax_Syntax.new_bv uu____5958 kres))
in (

let t = (

let uu____5963 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____5964 = (

let uu____5971 = (

let uu____5977 = (

let uu____5978 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp uu____5978))
in FStar_Util.Inl (uu____5977))
in Some (uu____5971))
in (FStar_Syntax_Util.abs bs uu____5963 uu____5964)))
in ((FStar_Syntax_Util.set_uvar u t);
((a), (Some (FStar_Syntax_Syntax.imp_tag)));
)))
end)))
end))
end))))
in (

let uu____5993 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], uu____6011) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e), (c))))
end
| uu____6023 -> begin
(

let uu____6031 = ((e), (c))
in (match (uu____6031) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (

let uu____6043 = (

let uu____6044 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in uu____6044.FStar_Syntax_Syntax.n)
in (match (uu____6043) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____6061 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____6061) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| uu____6071 -> begin
(FStar_Syntax_Util.arrow tvars c)
end))
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (

let uu____6081 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____6081)))))))
end))
end)
in (match (uu____5993) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs));
)))
end)))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> ((

let uu____6119 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6119) with
| true -> begin
(

let uu____6120 = (

let uu____6121 = (FStar_List.map (fun uu____6126 -> (match (uu____6126) with
| (lb, uu____6131, uu____6132) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____6121 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____6120))
end
| uu____6134 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____6142 -> (match (uu____6142) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____6157 = (

let uu____6164 = (FStar_All.pipe_right lecs (FStar_List.map (fun uu____6180 -> (match (uu____6180) with
| (uu____6186, e, c) -> begin
((e), (c))
end))))
in (gen env uu____6164))
in (match (uu____6157) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____6218 -> (match (uu____6218) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun uu____6262 uu____6263 -> (match (((uu____6262), (uu____6263))) with
| ((l, uu____6296, uu____6297), (us, e, c)) -> begin
((

let uu____6323 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____6323) with
| true -> begin
(

let uu____6324 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____6325 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____6326 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____6327 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" uu____6324 uu____6325 uu____6326 uu____6327)))))
end
| uu____6328 -> begin
()
end));
((l), (us), (e), (c));
)
end)) lecs ecs)
end))
in (FStar_List.map2 (fun univnames uu____6346 -> (match (uu____6346) with
| (l, generalized_univs, t, c) -> begin
(

let uu____6364 = (check_universe_generalization univnames generalized_univs t)
in ((l), (uu____6364), (t), (c)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env t1 t2 -> (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end
| uu____6396 -> begin
(

let uu____6397 = (FStar_TypeChecker_Rel.try_subtype env t1 t2)
in (match (uu____6397) with
| None -> begin
None
end
| Some (f) -> begin
(

let uu____6401 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____6401))
end))
end))
in (

let is_var = (fun e -> (

let uu____6407 = (

let uu____6408 = (FStar_Syntax_Subst.compress e)
in uu____6408.FStar_Syntax_Syntax.n)
in (match (uu____6407) with
| FStar_Syntax_Syntax.Tm_name (uu____6411) -> begin
true
end
| uu____6412 -> begin
false
end)))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___136_6434 = x
in {FStar_Syntax_Syntax.ppname = uu___136_6434.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_6434.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| uu____6435 -> begin
(

let uu___137_6436 = e
in (

let uu____6437 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = uu___137_6436.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu____6437; FStar_Syntax_Syntax.pos = uu___137_6436.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___137_6436.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let uu___138_6446 = env
in (

let uu____6447 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___138_6446.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___138_6446.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___138_6446.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___138_6446.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___138_6446.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___138_6446.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___138_6446.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___138_6446.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___138_6446.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___138_6446.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___138_6446.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___138_6446.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___138_6446.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___138_6446.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___138_6446.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____6447; FStar_TypeChecker_Env.is_iface = uu___138_6446.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___138_6446.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___138_6446.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___138_6446.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___138_6446.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___138_6446.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___138_6446.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___138_6446.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____6448 = (check env t1 t2)
in (match (uu____6448) with
| None -> begin
(

let uu____6452 = (

let uu____6453 = (

let uu____6456 = (FStar_TypeChecker_Err.expected_expression_of_type env t2 e t1)
in (

let uu____6457 = (FStar_TypeChecker_Env.get_range env)
in ((uu____6456), (uu____6457))))
in FStar_Errors.Error (uu____6453))
in (Prims.raise uu____6452))
end
| Some (g) -> begin
((

let uu____6462 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6462) with
| true -> begin
(

let uu____6463 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____6463))
end
| uu____6464 -> begin
()
end));
(

let uu____6465 = (decorate e t2)
in ((uu____6465), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> ((FStar_TypeChecker_Rel.force_trivial_guard env g);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____6489 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____6489) with
| true -> begin
(

let uu____6492 = (discharge g)
in (

let uu____6493 = (lc.FStar_Syntax_Syntax.comp ())
in ((uu____6492), (uu____6493))))
end
| uu____6498 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (

let uu____6505 = (

let uu____6506 = (

let uu____6507 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____6507 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____6506 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____6505 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let uu____6509 = (destruct_comp c)
in (match (uu____6509) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____6521 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____6522 = (

let uu____6523 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____6524 = (

let uu____6525 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6526 = (

let uu____6528 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6528)::[])
in (uu____6525)::uu____6526))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6523 uu____6524)))
in (uu____6522 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) uu____6521)))
in ((

let uu____6534 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____6534) with
| true -> begin
(

let uu____6535 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____6535))
end
| uu____6536 -> begin
()
end));
(

let g = (

let uu____6538 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g uu____6538))
in (

let uu____6539 = (discharge g)
in (

let uu____6540 = (FStar_Syntax_Syntax.mk_Comp c)
in ((uu____6539), (uu____6540)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f uu___95_6564 -> (match (uu___95_6564) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, uu____6570))::[] -> begin
(f fst)
end
| uu____6583 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____6588 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____6588 (fun _0_32 -> FStar_TypeChecker_Common.NonTrivial (_0_32)))))
in (

let op_or_e = (fun e -> (

let uu____6597 = (

let uu____6600 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____6600))
in (FStar_All.pipe_right uu____6597 (fun _0_33 -> FStar_TypeChecker_Common.NonTrivial (_0_33)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_34 -> FStar_TypeChecker_Common.NonTrivial (_0_34))))
in (

let op_or_t = (fun t -> (

let uu____6611 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____6611 (fun _0_35 -> FStar_TypeChecker_Common.NonTrivial (_0_35)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_36 -> FStar_TypeChecker_Common.NonTrivial (_0_36))))
in (

let short_op_ite = (fun uu___96_6625 -> (match (uu___96_6625) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____6631))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____6646))::[] -> begin
(

let uu____6667 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____6667 (fun _0_37 -> FStar_TypeChecker_Common.NonTrivial (_0_37))))
end
| uu____6672 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____6725 = (FStar_Util.find_map table (fun uu____6731 -> (match (uu____6731) with
| (x, mk) -> begin
(match ((FStar_Ident.lid_equals x lid)) with
| true -> begin
(

let uu____6744 = (mk seen_args)
in Some (uu____6744))
end
| uu____6745 -> begin
None
end)
end)))
in (match (uu____6725) with
| None -> begin
FStar_TypeChecker_Common.Trivial
end
| Some (g) -> begin
g
end)))
end
| uu____6747 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____6751 = (

let uu____6752 = (FStar_Syntax_Util.un_uinst l)
in uu____6752.FStar_Syntax_Syntax.n)
in (match (uu____6751) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| uu____6756 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, uu____6774))::uu____6775 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| uu____6781 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____6785, Some (FStar_Syntax_Syntax.Implicit (uu____6786))))::uu____6787 -> begin
bs
end
| uu____6796 -> begin
(

let uu____6797 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6797) with
| None -> begin
bs
end
| Some (t) -> begin
(

let uu____6800 = (

let uu____6801 = (FStar_Syntax_Subst.compress t)
in uu____6801.FStar_Syntax_Syntax.n)
in (match (uu____6800) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____6805) -> begin
(

let uu____6816 = (FStar_Util.prefix_until (fun uu___97_6835 -> (match (uu___97_6835) with
| (uu____6839, Some (FStar_Syntax_Syntax.Implicit (uu____6840))) -> begin
false
end
| uu____6842 -> begin
true
end)) bs')
in (match (uu____6816) with
| None -> begin
bs
end
| Some ([], uu____6860, uu____6861) -> begin
bs
end
| Some (imps, uu____6898, uu____6899) -> begin
(

let uu____6936 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____6944 -> (match (uu____6944) with
| (x, uu____6949) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____6936) with
| true -> begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun uu____6972 -> (match (uu____6972) with
| (x, i) -> begin
(

let uu____6983 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____6983), (i)))
end))))
in (FStar_List.append imps bs)))
end
| uu____6988 -> begin
bs
end))
end))
end
| uu____6989 -> begin
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
| uu____7007 -> begin
(

let uu____7008 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t)))))))) uu____7008 e.FStar_Syntax_Syntax.pos))
end))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____7034 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid))
in (match (uu____7034) with
| true -> begin
e
end
| uu____7035 -> begin
(

let uu____7036 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t)))))))) uu____7036 e.FStar_Syntax_Syntax.pos))
end))))


let effect_repr_aux = (fun only_reifiable env c u_c -> (

let uu____7078 = (

let uu____7080 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env uu____7080))
in (match (uu____7078) with
| None -> begin
None
end
| Some (ed) -> begin
(

let uu____7087 = (only_reifiable && (

let uu____7088 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____7088))))
in (match (uu____7087) with
| true -> begin
None
end
| uu____7095 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
None
end
| uu____7101 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let uu____7103 = (

let uu____7112 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (uu____7112)))
in (match (uu____7103) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____7146 = (

let uu____7149 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7150 = (

let uu____7153 = (

let uu____7154 = (

let uu____7164 = (

let uu____7166 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____7166)::(wp)::[])
in ((repr), (uu____7164)))
in FStar_Syntax_Syntax.Tm_app (uu____7154))
in (FStar_Syntax_Syntax.mk uu____7153))
in (uu____7150 None uu____7149)))
in Some (uu____7146)))
end)))
end)
end))
end)))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (

let uu____7210 = (

let uu____7211 = (

let uu____7214 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (

let uu____7215 = (FStar_TypeChecker_Env.get_range env)
in ((uu____7214), (uu____7215))))
in FStar_Errors.Error (uu____7211))
in (Prims.raise uu____7210)))
in (

let uu____7216 = (

let uu____7220 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env uu____7220 u_c))
in (match (uu____7216) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end))))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____7247 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____7247) with
| true -> begin
((d (FStar_Ident.text_of_lid lident));
(

let uu____7249 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) uu____7249));
)
end
| uu____7250 -> begin
()
end));
(

let fv = (

let uu____7252 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____7252 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]), ([])))
in (

let uu____7260 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv))) None FStar_Range.dummyRange)
in ((sig_ctx), (uu____7260)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun uu___98_7282 -> (match (uu___98_7282) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7283 -> begin
false
end))
in (

let reducibility = (fun uu___99_7287 -> (match (uu___99_7287) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____7288 -> begin
false
end))
in (

let assumption = (fun uu___100_7292 -> (match (uu___100_7292) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| uu____7293 -> begin
false
end))
in (

let reification = (fun uu___101_7297 -> (match (uu___101_7297) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| uu____7299 -> begin
false
end))
in (

let inferred = (fun uu___102_7303 -> (match (uu___102_7303) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| uu____7308 -> begin
false
end))
in (

let has_eq = (fun uu___103_7312 -> (match (uu___103_7312) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| uu____7313 -> begin
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
| uu____7338 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____7341 = (

let uu____7342 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___104_7344 -> (match (uu___104_7344) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____7345 -> begin
false
end))))
in (FStar_All.pipe_right uu____7342 Prims.op_Negation))
in (match (uu____7341) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (

let uu____7355 = (

let uu____7356 = (

let uu____7359 = (

let uu____7360 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____7360 msg))
in ((uu____7359), (r)))
in FStar_Errors.Error (uu____7356))
in (Prims.raise uu____7355)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun uu____7368 -> (err' ""))
in ((match (((FStar_List.length quals) <> (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____7374 -> begin
()
end);
(

let uu____7376 = (

let uu____7377 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____7377)))
in (match (uu____7376) with
| true -> begin
(err "ill-formed combination")
end
| uu____7379 -> begin
()
end));
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____7381), uu____7382, uu____7383, uu____7384, uu____7385) -> begin
((

let uu____7398 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____7398) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____7400 -> begin
()
end));
(

let uu____7401 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____7401) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____7404 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____7405) -> begin
(

let uu____7413 = (

let uu____7414 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____7414)))
in (match (uu____7413) with
| true -> begin
(err' ())
end
| uu____7417 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____7418) -> begin
(

let uu____7425 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____7425) with
| true -> begin
(err' ())
end
| uu____7427 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____7428) -> begin
(

let uu____7434 = (

let uu____7435 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption)))))
in (not (uu____7435)))
in (match (uu____7434) with
| true -> begin
(err' ())
end
| uu____7438 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____7439) -> begin
(

let uu____7442 = (

let uu____7443 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____7443)))
in (match (uu____7442) with
| true -> begin
(err' ())
end
| uu____7446 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____7447) -> begin
(

let uu____7450 = (

let uu____7451 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____7451)))
in (match (uu____7450) with
| true -> begin
(err' ())
end
| uu____7454 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7455) -> begin
(

let uu____7465 = (

let uu____7466 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____7466)))
in (match (uu____7465) with
| true -> begin
(err' ())
end
| uu____7469 -> begin
()
end))
end
| uu____7470 -> begin
()
end);
))))))
end
| uu____7471 -> begin
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

let uu____7527 = (

let uu____7530 = (

let uu____7531 = (

let uu____7536 = (

let uu____7537 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7537))
in ((uu____7536), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____7531))
in (FStar_Syntax_Syntax.mk uu____7530))
in (uu____7527 None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7563 -> (match (uu____7563) with
| (x, imp) -> begin
(

let uu____7570 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7570), (imp)))
end))))
in ((FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p)))
in (

let unrefined_arg_binder = (

let uu____7576 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____7576))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____7578 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational None)
in (

let uu____7585 = (

let uu____7586 = (

let uu____7587 = (

let uu____7588 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____7589 = (

let uu____7590 = (

let uu____7591 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7591))
in (uu____7590)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____7588 uu____7589)))
in (uu____7587 None p))
in (FStar_Syntax_Util.b2t uu____7586))
in (FStar_Syntax_Util.refine x uu____7585)))
in (

let uu____7596 = (

let uu___139_7597 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___139_7597.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___139_7597.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____7596)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____7607 = (FStar_List.map (fun uu____7617 -> (match (uu____7617) with
| (x, uu____7624) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____7607 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7648 -> (match (uu____7648) with
| (x, uu____7655) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = (match ((fvq <> FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____7660 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((

let uu____7664 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____7664)) || (

let uu____7665 = (

let uu____7666 = (FStar_TypeChecker_Env.current_module env)
in uu____7666.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____7665)))
in (

let quals = (

let uu____7669 = (

let uu____7671 = (

let uu____7673 = (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit))
in (match (uu____7673) with
| true -> begin
(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____7675 -> begin
[]
end))
in (

let uu____7676 = (FStar_List.filter (fun uu___105_7678 -> (match (uu___105_7678) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7679 -> begin
false
end)) iquals)
in (FStar_List.append uu____7671 uu____7676)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::[]
end
| uu____7681 -> begin
[]
end)) uu____7669))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____7692 = (

let uu____7693 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7693))
in (FStar_Syntax_Syntax.mk_Total uu____7692))
in (

let uu____7694 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____7694)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid discriminator_name))))
in ((

let uu____7698 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7698) with
| true -> begin
(

let uu____7699 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____7699))
end
| uu____7700 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____7702 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Const.exp_true_bool
end
| uu____7708 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____7731 -> (match (uu____7731) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____7747 = (

let uu____7750 = (

let uu____7751 = (

let uu____7756 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((uu____7756), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____7751))
in (pos uu____7750))
in ((uu____7747), (b)))
end
| uu____7759 -> begin
(

let uu____7760 = (

let uu____7763 = (

let uu____7764 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7764))
in (pos uu____7763))
in ((uu____7760), (b)))
end))
end))))
in (

let pat_true = (

let uu____7778 = (

let uu____7781 = (

let uu____7782 = (

let uu____7790 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((uu____7790), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____7782))
in (pos uu____7781))
in ((uu____7778), (None), (FStar_Syntax_Const.exp_true_bool)))
in (

let pat_false = (

let uu____7816 = (

let uu____7819 = (

let uu____7820 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7820))
in (pos uu____7819))
in ((uu____7816), (None), (FStar_Syntax_Const.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst unrefined_arg_binder))
in (

let uu____7831 = (

let uu____7834 = (

let uu____7835 = (

let uu____7851 = (

let uu____7853 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____7854 = (

let uu____7856 = (FStar_Syntax_Util.branch pat_false)
in (uu____7856)::[])
in (uu____7853)::uu____7854))
in ((arg_exp), (uu____7851)))
in FStar_Syntax_Syntax.Tm_match (uu____7835))
in (FStar_Syntax_Syntax.mk uu____7834))
in (uu____7831 None p))))))
end)
in (

let dd = (

let uu____7867 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____7867) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____7869 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____7877 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____7879 = (

let uu____7882 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd None)
in FStar_Util.Inr (uu____7882))
in (

let uu____7883 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____7879; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____7883}))
in (

let impl = (

let uu____7887 = (

let uu____7896 = (

let uu____7898 = (

let uu____7899 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____7899 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____7898)::[])
in ((((false), ((lb)::[]))), (p), (uu____7896), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____7887))
in ((

let uu____7915 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7915) with
| true -> begin
(

let uu____7916 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____7916))
end
| uu____7917 -> begin
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

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7936 -> (match (uu____7936) with
| (a, uu____7940) -> begin
(

let uu____7941 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____7941) with
| (field_name, uu____7945) -> begin
(

let field_proj_tm = (

let uu____7947 = (

let uu____7948 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7948))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7947 inst_univs))
in (

let proj = ((FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[])) None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____7964 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7973 -> (match (uu____7973) with
| (x, uu____7978) -> begin
(

let p = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____7980 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____7980) with
| (field_name, uu____7985) -> begin
(

let t = (

let uu____7987 = (

let uu____7988 = (

let uu____7991 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____7991))
in (FStar_Syntax_Util.arrow binders uu____7988))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____7987))
in (

let only_decl = (((

let uu____7993 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____7993)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____7994 = (

let uu____7995 = (FStar_TypeChecker_Env.current_module env)
in uu____7995.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____7994)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____8005 = (FStar_List.filter (fun uu___106_8007 -> (match (uu___106_8007) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____8008 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____8005)
end
| uu____8009 -> begin
q
end))
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___107_8016 -> (match (uu___107_8016) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____8017 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in ((

let uu____8021 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8021) with
| true -> begin
(

let uu____8022 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____8022))
end
| uu____8023 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____8025 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____8049 -> (match (uu____8049) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match (((i + ntps) = j)) with
| true -> begin
(

let uu____8065 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____8065), (b)))
end
| uu____8070 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____8077 = (

let uu____8080 = (

let uu____8081 = (

let uu____8086 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((uu____8086), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____8081))
in (pos uu____8080))
in ((uu____8077), (b)))
end
| uu____8089 -> begin
(

let uu____8090 = (

let uu____8093 = (

let uu____8094 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8094))
in (pos uu____8093))
in ((uu____8090), (b)))
end)
end))
end))))
in (

let pat = (

let uu____8106 = (

let uu____8109 = (

let uu____8110 = (

let uu____8118 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((uu____8118), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____8110))
in (pos uu____8109))
in (

let uu____8124 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____8106), (None), (uu____8124))))
in (

let body = (

let uu____8135 = (

let uu____8138 = (

let uu____8139 = (

let uu____8155 = (

let uu____8157 = (FStar_Syntax_Util.branch pat)
in (uu____8157)::[])
in ((arg_exp), (uu____8155)))
in FStar_Syntax_Syntax.Tm_match (uu____8139))
in (FStar_Syntax_Syntax.mk uu____8138))
in (uu____8135 None p))
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let dd = (

let uu____8174 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____8174) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____8176 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____8178 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____8180 = (

let uu____8183 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (uu____8183))
in (

let uu____8184 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____8180; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____8184}))
in (

let impl = (

let uu____8188 = (

let uu____8197 = (

let uu____8199 = (

let uu____8200 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____8200 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____8199)::[])
in ((((false), ((lb)::[]))), (p), (uu____8197), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____8188))
in ((

let uu____8216 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8216) with
| true -> begin
(

let uu____8217 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____8217))
end
| uu____8218 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____8220 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
)))))))
end)))
end))))
in (FStar_All.pipe_right uu____7964 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, quals, uu____8248, r) when (not ((FStar_Ident.lid_equals constr_lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____8254 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____8254) with
| (univ_opening, uvs) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____8267 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____8267) with
| (formals, uu____8277) -> begin
(

let uu____8288 = (

let tps_opt = (FStar_Util.find_map tcs (fun se -> (

let uu____8301 = (

let uu____8302 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals typ_lid uu____8302))
in (match (uu____8301) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____8311, uvs', tps, typ0, uu____8315, constrs, uu____8317, uu____8318) -> begin
Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____8332 -> begin
(failwith "Impossible")
end)
end
| uu____8337 -> begin
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
| uu____8364 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____8288) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ0 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____8374 = (FStar_Syntax_Util.arrow_formals typ0)
in (match (uu____8374) with
| (indices, uu____8384) -> begin
(

let refine_domain = (

let uu____8396 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___108_8398 -> (match (uu___108_8398) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8399) -> begin
true
end
| uu____8404 -> begin
false
end))))
in (match (uu____8396) with
| true -> begin
false
end
| uu____8405 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___109_8411 -> (match (uu___109_8411) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8413, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____8420 -> begin
None
end))
in (

let uu____8421 = (FStar_Util.find_map quals filter_records)
in (match (uu____8421) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)))
in (

let iquals = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____8427 -> begin
iquals
end)
in (

let fields = (

let uu____8429 = (FStar_Util.first_N n_typars formals)
in (match (uu____8429) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____8460 uu____8461 -> (match (((uu____8460), (uu____8461))) with
| ((x, uu____8471), (x', uu____8473)) -> begin
(

let uu____8478 = (

let uu____8483 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____8483)))
in FStar_Syntax_Syntax.NT (uu____8478))
end)) imp_tps inductive_tps)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals fv_qual refine_domain env typ_lid constr_lid uvs inductive_tps indices fields)))))
end))))
end))
end)))
end))
end
| uu____8484 -> begin
[]
end))




