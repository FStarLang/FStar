
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  unit = (fun env errs -> (

let uu____21 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____22 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.log_issue uu____21 uu____22))))


let new_implicit_var_aux : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.binding Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun reason r gamma binders k -> (

let ctx_uvar = (

let uu____79 = (FStar_Syntax_Unionfind.fresh ())
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____79; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = binders; FStar_Syntax_Syntax.ctx_uvar_typ = k; FStar_Syntax_Syntax.ctx_uvar_reason = reason; FStar_Syntax_Syntax.ctx_uvar_should_check = true; FStar_Syntax_Syntax.ctx_uvar_range = r})
in ((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true gamma binders);
(

let uu____91 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_uvar)) FStar_Pervasives_Native.None r)
in ((ctx_uvar), (uu____91)));
)))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (

let uu____128 = (FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid)
in (match (uu____128) with
| FStar_Pervasives_Native.Some ((uu____151)::((tm, uu____153))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| uu____203 -> begin
(

let binders = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____215 = (new_implicit_var_aux reason r env.FStar_TypeChecker_Env.gamma binders k)
in (match (uu____215) with
| (ctx_uvar, t) -> begin
(

let g = (

let uu___98_241 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___98_241.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___98_241.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___98_241.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (((reason), (t), (ctx_uvar), (r), (true)))::[]})
in ((t), ((((ctx_uvar), (r)))::[]), (g)))
end)))
end)))


let close_guard_implicits : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env xs g -> (

let rec aux = (fun x i -> (

let uu____338 = i
in (match (uu____338) with
| (reason, term, ctx_u, range, should_check) -> begin
(match ((not (should_check))) with
| true -> begin
i
end
| uu____384 -> begin
(

let uu____385 = (FStar_Syntax_Unionfind.find ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____385) with
| FStar_Pervasives_Native.Some (uu____400) -> begin
((

let uu____402 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____402) with
| true -> begin
(

let uu____403 = (FStar_Syntax_Print.ctx_uvar_to_string ctx_u)
in (FStar_Util.print1 "%s already solved; nothing to do" uu____403))
end
| uu____404 -> begin
()
end));
i;
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____405 = (FStar_Util.prefix_until (fun uu___79_420 -> (match (uu___79_420) with
| FStar_Syntax_Syntax.Binding_var (uu____421) -> begin
true
end
| uu____422 -> begin
false
end)) ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma)
in (match (uu____405) with
| FStar_Pervasives_Native.None -> begin
i
end
| FStar_Pervasives_Native.Some (uu____445, hd1, gamma_tail) -> begin
((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason range should_check ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders);
(match (hd1) with
| FStar_Syntax_Syntax.Binding_var (x') when (FStar_Syntax_Syntax.bv_eq x x') -> begin
(

let uu____480 = (FStar_Util.prefix ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____480) with
| (binders_pfx, uu____512) -> begin
(

let typ = (

let uu____536 = (

let uu____543 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____543)::[])
in (

let uu____556 = (FStar_Syntax_Syntax.mk_Total ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Syntax_Util.arrow uu____536 uu____556)))
in (

let uu____559 = (new_implicit_var_aux reason range gamma_tail binders_pfx typ)
in (match (uu____559) with
| (ctx_v, t_v) -> begin
(

let sol = (

let uu____587 = (

let uu____592 = (

let uu____593 = (

let uu____600 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____600))
in (uu____593)::[])
in (FStar_Syntax_Syntax.mk_Tm_app t_v uu____592))
in (uu____587 FStar_Pervasives_Native.None range))
in ((

let uu____616 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____616) with
| true -> begin
(

let uu____617 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____618 = (FStar_Syntax_Print.ctx_uvar_to_string ctx_u)
in (

let uu____619 = (FStar_Syntax_Print.term_to_string sol)
in (FStar_Util.print3 "Closing implicit %s with binder %s to %s\n" uu____617 uu____618 uu____619))))
end
| uu____620 -> begin
()
end));
(FStar_Syntax_Unionfind.change ctx_u.FStar_Syntax_Syntax.ctx_uvar_head sol);
((reason), (t_v), (ctx_v), (range), (should_check));
))
end)))
end))
end
| uu____624 -> begin
i
end);
)
end))
end))
end)
end)))
in (

let uu____625 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred (FStar_List.partition (fun uu____671 -> (match (uu____671) with
| (uu____676, p) -> begin
(FStar_TypeChecker_Rel.flex_prob_closing env xs p)
end))))
in (match (uu____625) with
| (solve_now, defer) -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env (

let uu___99_706 = g
in {FStar_TypeChecker_Env.guard_f = uu___99_706.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = solve_now; FStar_TypeChecker_Env.univ_ineqs = uu___99_706.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___99_706.FStar_TypeChecker_Env.implicits}))
in (

let g2 = (

let uu___100_708 = g1
in {FStar_TypeChecker_Env.guard_f = uu___100_708.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = defer; FStar_TypeChecker_Env.univ_ineqs = uu___100_708.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___100_708.FStar_TypeChecker_Env.implicits})
in ((

let uu____710 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____710) with
| true -> begin
(

let uu____711 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (FStar_Util.print1 "Starting to close implicits with binders {%s}\n" uu____711))
end
| uu____712 -> begin
()
end));
(

let is = (FStar_List.fold_right (fun uu____751 is -> (match (uu____751) with
| (x, uu____786) -> begin
((

let uu____788 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____788) with
| true -> begin
(

let uu____789 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print1 "Considering closing %s\n" uu____789))
end
| uu____790 -> begin
()
end));
(FStar_List.map (aux x) is);
)
end)) xs g2.FStar_TypeChecker_Env.implicits)
in (

let g3 = (

let uu___101_816 = g2
in {FStar_TypeChecker_Env.guard_f = uu___101_816.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___101_816.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___101_816.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = is})
in ((

let uu____818 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____818) with
| true -> begin
(

let uu____819 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____820 = (FStar_TypeChecker_Rel.guard_to_string env g3)
in (FStar_Util.print2 "Closed implicits with binders {%s}; guard is\n\t%s\n" uu____819 uu____820)))
end
| uu____821 -> begin
()
end));
g3;
)));
)))
end))))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____835 = (

let uu____836 = (FStar_Util.set_is_empty uvs)
in (not (uu____836)))
in (match (uu____835) with
| true -> begin
(

let us = (

let uu____838 = (

let uu____841 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun u -> (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)) uu____841))
in (FStar_All.pipe_right uu____838 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____852 = (

let uu____857 = (

let uu____858 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____858))
in ((FStar_Errors.Error_UncontrainedUnificationVar), (uu____857)))
in (FStar_Errors.log_issue r uu____852));
(FStar_Options.pop ());
))
end
| uu____859 -> begin
()
end))))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____875 -> (match (uu____875) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____885; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____887; FStar_Syntax_Syntax.lbpos = uu____888} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____921 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 e)
in (match (uu____921) with
| (univ_vars2, e1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars2)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let rec aux = (fun e2 -> (

let e3 = (FStar_Syntax_Subst.compress e2)
in (match (e3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e4, uu____958) -> begin
(aux e4)
end
| FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____965) -> begin
(FStar_Pervasives_Native.fst t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1020) -> begin
(

let res = (aux body)
in (

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____1052 = (FStar_Options.ml_ish ())
in (match (uu____1052) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____1055 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in ((

let uu____1069 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____1069) with
| true -> begin
(

let uu____1070 = (FStar_Range.string_of_range r)
in (

let uu____1071 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Using type %s\n" uu____1070 uu____1071)))
end
| uu____1072 -> begin
()
end));
FStar_Util.Inl (t2);
))))
end
| uu____1073 -> begin
FStar_Util.Inl (FStar_Syntax_Syntax.tun)
end)))
in (

let t2 = (

let uu____1075 = (aux e1)
in (match (uu____1075) with
| FStar_Util.Inr (c) -> begin
(

let uu____1081 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____1081) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1082 -> begin
(

let uu____1083 = (

let uu____1088 = (

let uu____1089 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____1089))
in ((FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec), (uu____1088)))
in (FStar_Errors.raise_error uu____1083 rng))
end))
end
| FStar_Util.Inl (t2) -> begin
t2
end))
in ((univ_vars2), (t2), (true))))))
end))
end
| uu____1093 -> begin
(

let uu____1094 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____1094) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let pat_as_exp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t))  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p tc_annot -> (

let check_bv = (fun env1 x -> (

let uu____1188 = (

let uu____1193 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in (match (uu____1193) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____1198; FStar_Syntax_Syntax.vars = uu____1199} -> begin
(

let uu____1202 = (FStar_Syntax_Util.type_u ())
in (match (uu____1202) with
| (t, uu____1212) -> begin
(

let uu____1213 = (

let uu____1226 = (FStar_Syntax_Syntax.range_of_bv x)
in (new_implicit_var "" uu____1226 env1 t))
in (match (uu____1213) with
| (t1, uu____1232, g) -> begin
((t1), (g))
end))
end))
end
| t -> begin
(tc_annot env1 t)
end))
in (match (uu____1188) with
| (t_x, guard) -> begin
(((

let uu___102_1254 = x
in {FStar_Syntax_Syntax.ppname = uu___102_1254.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_1254.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (guard))
end)))
in (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env1 p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = (match (c) with
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(FStar_ToSyntax_ToSyntax.desugar_machine_integer env1.FStar_TypeChecker_Env.dsenv repr sw p1.FStar_Syntax_Syntax.p)
end
| uu____1329 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
end)
in (([]), ([]), ([]), (env1), (e), (FStar_TypeChecker_Rel.trivial_guard), (p1)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____1337) -> begin
(

let uu____1342 = (FStar_Syntax_Util.type_u ())
in (match (uu____1342) with
| (k, uu____1368) -> begin
(

let uu____1369 = (

let uu____1382 = (FStar_Syntax_Syntax.range_of_bv x)
in (new_implicit_var "" uu____1382 env1 k))
in (match (uu____1369) with
| (t, uu____1404, g) -> begin
(

let x1 = (

let uu___103_1419 = x
in {FStar_Syntax_Syntax.ppname = uu___103_1419.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___103_1419.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____1420 = (

let uu____1433 = (FStar_Syntax_Syntax.range_of_bv x1)
in (new_implicit_var "" uu____1433 env1 t))
in (match (uu____1420) with
| (e, uu____1455, g') -> begin
(

let p2 = (

let uu___104_1472 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (e))); FStar_Syntax_Syntax.p = uu___104_1472.FStar_Syntax_Syntax.p})
in (

let uu____1475 = (FStar_TypeChecker_Rel.conj_guard g g')
in (([]), ([]), ([]), (env1), (e), (uu____1475), (p2))))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____1483 = (check_bv env1 x)
in (match (uu____1483) with
| (x1, g) -> begin
(

let env2 = (match (allow_wc_dependence) with
| true -> begin
(FStar_TypeChecker_Env.push_bv env1 x1)
end
| uu____1511 -> begin
env1
end)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x1)) FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p)
in (((x1)::[]), ([]), ((x1)::[]), (env2), (e), (g), (p1))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____1522 = (check_bv env1 x)
in (match (uu____1522) with
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

let uu____1577 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1723 uu____1724 -> (match (((uu____1723), (uu____1724))) with
| ((b, a, w, env2, args, guard, pats1), (p2, imp)) -> begin
(

let uu____1922 = (pat_as_arg_with_env allow_wc_dependence env2 p2)
in (match (uu____1922) with
| (b', a', w', env3, te, guard', pat) -> begin
(

let arg = (match (imp) with
| true -> begin
(FStar_Syntax_Syntax.iarg te)
end
| uu____1997 -> begin
(FStar_Syntax_Syntax.as_arg te)
end)
in (

let uu____1998 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (((b')::b), ((a')::a), ((w')::w), (env3), ((arg)::args), (uu____1998), ((((pat), (imp)))::pats1))))
end))
end)) (([]), ([]), ([]), (env1), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([]))))
in (match (uu____1577) with
| (b, a, w, env2, args, guard, pats1) -> begin
(

let e = (

let uu____2141 = (

let uu____2146 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____2147 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app uu____2146 uu____2147)))
in (uu____2141 FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p))
in (

let uu____2164 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (

let uu____2175 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (

let uu____2186 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((uu____2164), (uu____2175), (uu____2186), (env2), (e), (guard), ((

let uu___105_2204 = p1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___105_2204.FStar_Syntax_Syntax.p})))))))
end))
end))
in (

let rec elaborate_pat = (fun env1 p1 -> (

let maybe_dot = (fun inaccessible a r -> (match ((allow_implicits && inaccessible)) with
| true -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) r)
end
| uu____2258 -> begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) r)
end))
in (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats1 = (FStar_List.map (fun uu____2304 -> (match (uu____2304) with
| (p2, imp) -> begin
(

let uu____2323 = (elaborate_pat env1 p2)
in ((uu____2323), (imp)))
end)) pats)
in (

let uu____2328 = (FStar_TypeChecker_Env.lookup_datacon env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2328) with
| (uu____2335, t) -> begin
(

let uu____2337 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2337) with
| (f, uu____2353) -> begin
(

let rec aux = (fun formals pats2 -> (match (((formals), (pats2))) with
| ([], []) -> begin
[]
end
| ([], (uu____2479)::uu____2480) -> begin
(

let uu____2523 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_TooManyPatternArguments), ("Too many pattern arguments")) uu____2523))
end
| ((uu____2532)::uu____2533, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun uu____2611 -> (match (uu____2611) with
| (t1, imp) -> begin
(match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (

let uu____2638 = (

let uu____2641 = (FStar_Syntax_Syntax.range_of_bv t1)
in FStar_Pervasives_Native.Some (uu____2641))
in (FStar_Syntax_Syntax.new_bv uu____2638 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____2643 = (maybe_dot inaccessible a r)
in ((uu____2643), (true)))))
end
| uu____2648 -> begin
(

let uu____2651 = (

let uu____2656 = (

let uu____2657 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" uu____2657))
in ((FStar_Errors.Fatal_InsufficientPatternArguments), (uu____2656)))
in (

let uu____2658 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Errors.raise_error uu____2651 uu____2658)))
end)
end))))
end
| ((f1)::formals', ((p2, p_imp))::pats') -> begin
(match (f1) with
| (uu____2732, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____2733))) when p_imp -> begin
(

let uu____2736 = (aux formals' pats')
in (((p2), (true)))::uu____2736)
end
| (uu____2753, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p2.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p3 = (

let uu____2761 = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (maybe_dot inaccessible a uu____2761))
in (

let uu____2762 = (aux formals' pats2)
in (((p3), (true)))::uu____2762)))
end
| (uu____2779, imp) -> begin
(

let uu____2785 = (

let uu____2792 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p2), (uu____2792)))
in (

let uu____2795 = (aux formals' pats')
in (uu____2785)::uu____2795))
end)
end))
in (

let uu___106_2810 = p1
in (

let uu____2813 = (

let uu____2814 = (

let uu____2827 = (aux f pats1)
in ((fv), (uu____2827)))
in FStar_Syntax_Syntax.Pat_cons (uu____2814))
in {FStar_Syntax_Syntax.v = uu____2813; FStar_Syntax_Syntax.p = uu___106_2810.FStar_Syntax_Syntax.p})))
end))
end)))
end
| uu____2844 -> begin
p1
end)))
in (

let one_pat = (fun allow_wc_dependence env1 p1 -> (

let p2 = (elaborate_pat env1 p1)
in (

let uu____2886 = (pat_as_arg_with_env allow_wc_dependence env1 p2)
in (match (uu____2886) with
| (b, a, w, env2, arg, guard, p3) -> begin
(

let uu____2944 = (FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))
in (match (uu____2944) with
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2970 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in (FStar_Errors.raise_error uu____2970 p3.FStar_Syntax_Syntax.p))
end
| uu____2993 -> begin
((b), (a), (w), (arg), (guard), (p3))
end))
end))))
in (

let uu____3002 = (one_pat true env p)
in (match (uu____3002) with
| (b, uu____3032, uu____3033, tm, guard, p1) -> begin
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
| (uu____3095, FStar_Syntax_Syntax.Tm_uinst (e2, uu____3097)) -> begin
(aux p1 e2)
end
| (FStar_Syntax_Syntax.Pat_constant (uu____3102), uu____3103) -> begin
(pkg p1.FStar_Syntax_Syntax.v)
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____3107 = (

let uu____3108 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3109 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____3108 uu____3109)))
in (failwith uu____3107))
end
| uu____3110 -> begin
()
end);
(

let uu____3112 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat")))
in (match (uu____3112) with
| true -> begin
(

let uu____3113 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3114 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" uu____3113 uu____3114)))
end
| uu____3115 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___107_3118 = x
in {FStar_Syntax_Syntax.ppname = uu___107_3118.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_3118.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
((

let uu____3122 = (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation)
in (match (uu____3122) with
| true -> begin
(

let uu____3123 = (

let uu____3124 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3125 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" uu____3124 uu____3125)))
in (failwith uu____3123))
end
| uu____3126 -> begin
()
end));
(

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___108_3129 = x
in {FStar_Syntax_Syntax.ppname = uu___108_3129.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___108_3129.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x1)))));
)
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, uu____3131), uu____3132) -> begin
(pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e1)))))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
((

let uu____3156 = (

let uu____3157 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (not (uu____3157)))
in (match (uu____3156) with
| true -> begin
(

let uu____3158 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3158))
end
| uu____3159 -> begin
()
end));
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____3177; FStar_Syntax_Syntax.vars = uu____3178}, args)) -> begin
((

let uu____3217 = (

let uu____3218 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____3218 Prims.op_Negation))
in (match (uu____3217) with
| true -> begin
(

let uu____3219 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3219))
end
| uu____3220 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____3357))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3432)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3469) -> begin
(

let pat = (

let uu____3491 = (aux argpat e2)
in (

let uu____3492 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3491), (uu____3492))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3497 -> begin
(

let uu____3520 = (

let uu____3521 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3522 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3521 uu____3522)))
in (failwith uu____3520))
end))
in (match_args [] args argpats)));
)
end
| (FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.pos = uu____3532; FStar_Syntax_Syntax.vars = uu____3533}, uu____3534); FStar_Syntax_Syntax.pos = uu____3535; FStar_Syntax_Syntax.vars = uu____3536}, args)) -> begin
((

let uu____3579 = (

let uu____3580 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right uu____3580 Prims.op_Negation))
in (match (uu____3579) with
| true -> begin
(

let uu____3581 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith uu____3581))
end
| uu____3582 -> begin
()
end));
(

let fv1 = fv'
in (

let rec match_args = (fun matched_pats args1 argpats1 -> (match (((args1), (argpats1))) with
| ([], []) -> begin
(pkg (FStar_Syntax_Syntax.Pat_cons (((fv1), ((FStar_List.rev matched_pats))))))
end
| ((arg)::args2, ((argpat, uu____3719))::argpats2) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e2, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (uu____3794)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e2)))) p1.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args2 argpats2)))
end
| ((e2, imp), uu____3831) -> begin
(

let pat = (

let uu____3853 = (aux argpat e2)
in (

let uu____3854 = (FStar_Syntax_Syntax.is_implicit imp)
in ((uu____3853), (uu____3854))))
in (match_args ((pat)::matched_pats) args2 argpats2))
end)
end
| uu____3859 -> begin
(

let uu____3882 = (

let uu____3883 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____3884 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" uu____3883 uu____3884)))
in (failwith uu____3882))
end))
in (match_args [] args argpats)));
)
end
| uu____3891 -> begin
(

let uu____3896 = (

let uu____3897 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (

let uu____3898 = (FStar_Syntax_Print.pat_to_string qq)
in (

let uu____3899 = (FStar_Syntax_Print.term_to_string exp)
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" uu____3897 uu____3898 uu____3899))))
in (failwith uu____3896))
end))))
in (aux p exp))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____3942 -> (match (uu____3942) with
| (p, i) -> begin
(

let uu____3959 = (decorated_pattern_as_term p)
in (match (uu____3959) with
| (vars, te) -> begin
(

let uu____3982 = (

let uu____3987 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____3987)))
in ((vars), (uu____3982)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4001 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____4001)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____4005 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____4005)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____4009 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____4009)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____4030 = (

let uu____4047 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____4047 FStar_List.unzip))
in (match (uu____4030) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____4169 = (

let uu____4170 = (

let uu____4171 = (

let uu____4186 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____4186), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____4171))
in (mk1 uu____4170))
in ((vars1), (uu____4169))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let comp_univ_opt : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____4222, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.GTotal (uu____4232, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::uu____4246 -> begin
FStar_Pervasives_Native.Some (hd1)
end)
end))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____4268))::[] -> begin
wp
end
| uu____4285 -> begin
(

let uu____4294 = (

let uu____4295 = (

let uu____4296 = (FStar_List.map (fun uu____4306 -> (match (uu____4306) with
| (x, uu____4312) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____4296 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____4295))
in (failwith uu____4294))
end)
in (

let uu____4315 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____4315), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____4331 = (destruct_comp c)
in (match (uu____4331) with
| (u, uu____4339, wp) -> begin
(

let uu____4341 = (

let uu____4350 = (

let uu____4357 = (lift.FStar_TypeChecker_Env.mlift_wp u c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____4357))
in (uu____4350)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____4341; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____4385 = (

let uu____4392 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____4393 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____4392 uu____4393)))
in (match (uu____4385) with
| (m, uu____4395, uu____4396) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____4412 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____4412) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____4413 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____4455 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____4455) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____4492 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____4492) with
| (a, kwp) -> begin
(

let uu____4523 = (destruct_comp m1)
in (

let uu____4530 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____4523), (uu____4530))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags1 -> (

let uu____4610 = (

let uu____4611 = (

let uu____4620 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4620)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____4611; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp uu____4610)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags1 -> (

let uu____4696 = (FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)
in (match (uu____4696) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____4697 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1)
end)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu____4708 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4708 lc.FStar_Syntax_Syntax.cflags (fun uu____4711 -> (

let uu____4712 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Subst.subst_comp subst1 uu____4712))))))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4718 = (

let uu____4719 = (FStar_Syntax_Subst.compress t)
in uu____4719.FStar_Syntax_Syntax.n)
in (match (uu____4718) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4722) -> begin
true
end
| uu____4735 -> begin
false
end)))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (reason1) -> begin
(

let uu____4792 = (

let uu____4793 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____4793))
in (match (uu____4792) with
| true -> begin
f
end
| uu____4794 -> begin
(

let uu____4795 = (reason1 ())
in (label uu____4795 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___109_4812 = g
in (

let uu____4813 = (

let uu____4814 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____4814))
in {FStar_TypeChecker_Env.guard_f = uu____4813; FStar_TypeChecker_Env.deferred = uu___109_4812.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___109_4812.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___109_4812.FStar_TypeChecker_Env.implicits}))
end))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____4834 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4834) with
| true -> begin
c
end
| uu____4835 -> begin
(

let uu____4836 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4836) with
| true -> begin
c
end
| uu____4837 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____4895 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4895)::[])
in (

let us = (

let uu____4911 = (

let uu____4914 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____4914)::[])
in (u_res)::uu____4911)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____4920 = (

let uu____4925 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____4926 = (

let uu____4927 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4934 = (

let uu____4943 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____4950 = (

let uu____4959 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____4959)::[])
in (uu____4943)::uu____4950))
in (uu____4927)::uu____4934))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4925 uu____4926)))
in (uu____4920 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____4993 = (destruct_comp c1)
in (match (uu____4993) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end)))


let close_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____5028 -> (

let uu____5029 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (close_comp env bvs uu____5029)))))


let should_not_inline_lc : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___80_5038 -> (match (uu___80_5038) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____5039 -> begin
false
end)))))


let should_return : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun env eopt lc -> (match (eopt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (e) -> begin
((((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) && (

let uu____5061 = (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____5061)))) && (

let uu____5068 = (FStar_Syntax_Util.head_and_args' e)
in (match (uu____5068) with
| (head1, uu____5082) -> begin
(

let uu____5099 = (

let uu____5100 = (FStar_Syntax_Util.un_uinst head1)
in uu____5100.FStar_Syntax_Syntax.n)
in (match (uu____5099) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5104 = (

let uu____5105 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_irreducible env uu____5105))
in (not (uu____5104)))
end
| uu____5106 -> begin
true
end))
end))) && (

let uu____5108 = (should_not_inline_lc lc)
in (not (uu____5108))))
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp = (fun env u_t_opt t v1 -> (

let c = (

let uu____5142 = (

let uu____5143 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____5143))
in (match (uu____5142) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____5144 -> begin
(

let uu____5145 = (FStar_Syntax_Util.is_unit t)
in (match (uu____5145) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero)))
end
| uu____5146 -> begin
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

let uu____5151 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5151) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____5152 -> begin
(

let uu____5153 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____5153) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____5163 = (

let uu____5164 = (

let uu____5169 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____5170 = (

let uu____5171 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____5178 = (

let uu____5187 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____5187)::[])
in (uu____5171)::uu____5178))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5169 uu____5170)))
in (uu____5164 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env uu____5163)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
end))
in ((

let uu____5215 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____5215) with
| true -> begin
(

let uu____5216 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____5217 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____5218 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____5216 uu____5217 uu____5218))))
end
| uu____5219 -> begin
()
end));
c;
)))


let weaken_flags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags1 -> (

let uu____5231 = (FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___81_5235 -> (match (uu___81_5235) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____5236 -> begin
false
end))))
in (match (uu____5231) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____5239 -> begin
(FStar_All.pipe_right flags1 (FStar_List.collect (fun uu___82_5245 -> (match (uu___82_5245) with
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

let uu____5264 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____5264) with
| true -> begin
c
end
| uu____5265 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____5267 = (destruct_comp c1)
in (match (uu____5267) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5281 = (

let uu____5286 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____5287 = (

let uu____5288 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5295 = (

let uu____5304 = (FStar_Syntax_Syntax.as_arg formula)
in (

let uu____5311 = (

let uu____5320 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5320)::[])
in (uu____5304)::uu____5311))
in (uu____5288)::uu____5295))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5286 uu____5287)))
in (uu____5281 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (

let uu____5353 = (weaken_flags c1.FStar_Syntax_Syntax.flags)
in (mk_comp md u_res_t res_t wp1 uu____5353))))
end)))
end)))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____5376 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let uu____5378 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5378) with
| true -> begin
c
end
| uu____5379 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(weaken_comp env c f1)
end)
end))))
in (

let uu____5381 = (weaken_flags lc.FStar_Syntax_Syntax.cflags)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ uu____5381 weaken))))


let strengthen_comp : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun env reason c f flags1 -> (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____5422 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____5424 = (destruct_comp c1)
in (match (uu____5424) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____5438 = (

let uu____5443 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____5444 = (

let uu____5445 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____5452 = (

let uu____5461 = (

let uu____5468 = (

let uu____5469 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____5469 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5468))
in (

let uu____5476 = (

let uu____5485 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5485)::[])
in (uu____5461)::uu____5476))
in (uu____5445)::uu____5452))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5443 uu____5444)))
in (uu____5438 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 flags1)))
end)))
end))


let strengthen_precondition : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e_for_debug_only lc g0 -> (

let uu____5560 = (FStar_TypeChecker_Rel.is_trivial g0)
in (match (uu____5560) with
| true -> begin
((lc), (g0))
end
| uu____5565 -> begin
(

let flags1 = (

let uu____5569 = (

let uu____5576 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____5576) with
| true -> begin
((true), ((FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]))
end
| uu____5585 -> begin
((false), ([]))
end))
in (match (uu____5569) with
| (maybe_trivial_post, flags1) -> begin
(

let uu____5596 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___83_5604 -> (match (uu___83_5604) with
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
| uu____5607 -> begin
[]
end))))
in (FStar_List.append flags1 uu____5596))
end))
in (

let strengthen = (fun uu____5613 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____5615 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____5617 = (FStar_TypeChecker_Rel.guard_form g01)
in (match (uu____5617) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____5620 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5620) with
| true -> begin
(

let uu____5621 = (FStar_TypeChecker_Normalize.term_to_string env e_for_debug_only)
in (

let uu____5622 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____5621 uu____5622)))
end
| uu____5623 -> begin
()
end));
(strengthen_comp env reason c f flags1);
)
end)))
end)))
in (

let uu____5624 = (

let uu____5625 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____5625 lc.FStar_Syntax_Syntax.res_typ flags1 strengthen))
in ((uu____5624), ((

let uu___110_5627 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___110_5627.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___110_5627.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___110_5627.FStar_TypeChecker_Env.implicits}))))))
end)))


let lcomp_has_trivial_postcondition : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) || (FStar_Util.for_some (fun uu___84_5634 -> (match (uu___84_5634) with
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
true
end
| uu____5635 -> begin
false
end)) lc.FStar_Syntax_Syntax.cflags)))


let maybe_add_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env uopt lc e -> (

let uu____5662 = ((FStar_Syntax_Util.is_lcomp_partial_return lc) || env.FStar_TypeChecker_Env.lax)
in (match (uu____5662) with
| true -> begin
e
end
| uu____5665 -> begin
(

let uu____5666 = ((lcomp_has_trivial_postcondition lc) && (

let uu____5668 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____5668)))
in (match (uu____5666) with
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
| uu____5691 -> begin
e
end))
end)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____5718 -> (match (uu____5718) with
| (b, lc2) -> begin
(

let debug1 = (fun f -> (

let uu____5738 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____5738) with
| true -> begin
(f ())
end
| uu____5739 -> begin
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

let uu____5746 = ((should_not_inline_lc lc11) || (should_not_inline_lc lc21))
in (match (uu____5746) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____5749 -> begin
(

let flags1 = (

let uu____5753 = (FStar_Syntax_Util.is_total_lcomp lc11)
in (match (uu____5753) with
| true -> begin
(

let uu____5756 = (FStar_Syntax_Util.is_total_lcomp lc21)
in (match (uu____5756) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____5759 -> begin
(

let uu____5760 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
in (match (uu____5760) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5763 -> begin
[]
end))
end))
end
| uu____5764 -> begin
(

let uu____5765 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) && (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21))
in (match (uu____5765) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5768 -> begin
[]
end))
end))
in (

let uu____5769 = (lcomp_has_trivial_postcondition lc21)
in (match (uu____5769) with
| true -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::flags1
end
| uu____5772 -> begin
flags1
end)))
end))
in (

let bind_it = (fun uu____5778 -> (

let uu____5779 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5779) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____5781 -> begin
(

let c1 = (FStar_Syntax_Syntax.lcomp_comp lc11)
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp lc21)
in ((debug1 (fun uu____5793 -> (

let uu____5794 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____5795 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____5797 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n" uu____5794 uu____5795 uu____5797))))));
(

let aux = (fun uu____5811 -> (

let uu____5812 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____5812) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____5833) -> begin
(

let uu____5834 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____5834) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____5847 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____5852 -> begin
(

let uu____5853 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____5853) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____5866 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun e1opt1 reason -> (match (((e1opt1), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____5924 = (

let uu____5929 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____5929), (reason)))
in FStar_Util.Inl (uu____5924))
end
| uu____5936 -> begin
(aux ())
end))
in (

let try_simplify = (fun uu____5960 -> (

let rec maybe_close = (fun t x c -> (

let uu____5977 = (

let uu____5978 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in uu____5978.FStar_Syntax_Syntax.n)
in (match (uu____5977) with
| FStar_Syntax_Syntax.Tm_refine (y, uu____5982) -> begin
(maybe_close y.FStar_Syntax_Syntax.sort x c)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____5988 -> begin
c
end)))
in (

let uu____5989 = (

let uu____5990 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____5990))
in (match (uu____5989) with
| true -> begin
(

let uu____6001 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____6001) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____6014 -> begin
(

let uu____6015 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonTrivialPreConditionInPrims), ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")) uu____6015))
end))
end
| uu____6024 -> begin
(

let uu____6025 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____6025) with
| true -> begin
(subst_c2 e1opt "both total")
end
| uu____6034 -> begin
(

let uu____6035 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____6035) with
| true -> begin
(

let uu____6044 = (

let uu____6049 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____6049), ("both gtot")))
in FStar_Util.Inl (uu____6044))
end
| uu____6054 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____6073 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____6075 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____6075))))
in (match (uu____6073) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___111_6088 = x
in {FStar_Syntax_Syntax.ppname = uu___111_6088.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___111_6088.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____6089 = (

let uu____6094 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____6094), ("c1 Tot")))
in FStar_Util.Inl (uu____6089))))
end
| uu____6099 -> begin
(aux ())
end))
end
| uu____6100 -> begin
(aux ())
end)
end))
end))
end))))
in (

let uu____6109 = (try_simplify ())
in (match (uu____6109) with
| FStar_Util.Inl (c, reason) -> begin
((debug1 (fun uu____6129 -> (

let uu____6130 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "(2) bind: Simplified (because %s) to\n\t%s\n" reason uu____6130))));
c;
)
end
| FStar_Util.Inr (reason) -> begin
((debug1 (fun uu____6139 -> (FStar_Util.print1 "(2) bind: Not simplified because %s\n" reason)));
(

let mk_bind = (fun c11 b1 c21 -> (

let uu____6160 = (lift_and_destruct env c11 c21)
in (match (uu____6160) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b1) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6213 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____6213)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____6227 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6227)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____6254 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____6261 = (

let uu____6270 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____6277 = (

let uu____6286 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____6293 = (

let uu____6302 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____6309 = (

let uu____6318 = (

let uu____6325 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____6325))
in (uu____6318)::[])
in (uu____6302)::uu____6309))
in (uu____6286)::uu____6293))
in (uu____6270)::uu____6277))
in (uu____6254)::uu____6261))
in (

let wp = (

let uu____6365 = (

let uu____6370 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6370 wp_args))
in (uu____6365 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (mk_comp md u_t2 t2 wp bind_flags))))))
end)))
in (

let mk_seq = (fun c11 b1 c21 -> (

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in (

let uu____6395 = (FStar_TypeChecker_Env.join env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____6395) with
| (m, uu____6403, lift2) -> begin
(

let c23 = (

let uu____6406 = (lift_comp c22 m lift2)
in (FStar_Syntax_Syntax.mk_Comp uu____6406))
in (

let uu____6407 = (destruct_comp c12)
in (match (uu____6407) with
| (u1, t1, wp1) -> begin
(

let md_pure_or_ghost = (FStar_TypeChecker_Env.get_effect_decl env c12.FStar_Syntax_Syntax.effect_name)
in (

let vc1 = (

let uu____6421 = (

let uu____6426 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u1)::[]) env md_pure_or_ghost md_pure_or_ghost.FStar_Syntax_Syntax.trivial)
in (

let uu____6427 = (

let uu____6428 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____6435 = (

let uu____6444 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____6444)::[])
in (uu____6428)::uu____6435))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6426 uu____6427)))
in (uu____6421 FStar_Pervasives_Native.None r1))
in (strengthen_comp env FStar_Pervasives_Native.None c23 vc1 bind_flags)))
end)))
end)))))
in (

let c1_typ = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____6475 = (destruct_comp c1_typ)
in (match (uu____6475) with
| (u_res_t1, res_t1, uu____6484) -> begin
(

let uu____6485 = ((FStar_Option.isSome b) && (should_return env e1opt lc11))
in (match (uu____6485) with
| true -> begin
(

let e1 = (FStar_Option.get e1opt)
in (

let x = (FStar_Option.get b)
in (

let uu____6488 = (FStar_Syntax_Util.is_partial_return c1)
in (match (uu____6488) with
| true -> begin
((debug1 (fun uu____6496 -> (

let uu____6497 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____6498 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case a): Substituting %s for %s" uu____6497 uu____6498)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (mk_bind c1 b c21));
)
end
| uu____6502 -> begin
(

let uu____6503 = (((FStar_Options.vcgen_optimize_bind_as_seq ()) && (lcomp_has_trivial_postcondition lc11)) && (

let uu____6505 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____6505)))
in (match (uu____6503) with
| true -> begin
(

let e1' = (

let uu____6525 = (FStar_Options.vcgen_decorate_with_type ())
in (match (uu____6525) with
| true -> begin
(FStar_Syntax_Util.mk_with_type u_res_t1 res_t1 e1)
end
| uu____6526 -> begin
e1
end))
in ((debug1 (fun uu____6534 -> (

let uu____6535 = (FStar_TypeChecker_Normalize.term_to_string env e1')
in (

let uu____6536 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case b): Substituting %s for %s" uu____6535 uu____6536)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1'))))::[]) c2)
in (mk_seq c1 b c21));
))
end
| uu____6540 -> begin
((debug1 (fun uu____6548 -> (

let uu____6549 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____6550 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case c): Adding equality %s = %s" uu____6549 uu____6550)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (

let x_eq_e = (

let uu____6555 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq2 u_res_t1 res_t1 e1 uu____6555))
in (

let c22 = (weaken_comp env c21 x_eq_e)
in (mk_bind c1 b c22))));
)
end))
end))))
end
| uu____6557 -> begin
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
| uu____6571 -> begin
g2
end))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let should_return1 = ((((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)) && (should_return env (FStar_Pervasives_Native.Some (e)) lc)) && (

let uu____6593 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____6593))))
in (

let flags1 = (match (should_return1) with
| true -> begin
(

let uu____6599 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____6599) with
| true -> begin
(FStar_Syntax_Syntax.RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____6602 -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end))
end
| uu____6603 -> begin
lc.FStar_Syntax_Syntax.cflags
end)
in (

let refine1 = (fun uu____6611 -> (

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

let uu____6615 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____6615) with
| true -> begin
(

let retc = (return_value env (FStar_Pervasives_Native.Some (u_t)) (FStar_Syntax_Util.comp_result c) e)
in (

let uu____6619 = (

let uu____6620 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____6620)))
in (match (uu____6619) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___112_6625 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___112_6625.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___112_6625.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___112_6625.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____6626 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags1)
end)))
end
| uu____6627 -> begin
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

let uu____6636 = (

let uu____6637 = (return_value env (FStar_Pervasives_Native.Some (u_t)) t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____6637 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6636))
in (

let eq1 = (FStar_Syntax_Util.mk_eq2 u_t t xexp e)
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____6640 = (

let uu____6641 = (

let uu____6642 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None uu____6642 ((FStar_Pervasives_Native.Some (x)), (eq_ret))))
in (FStar_Syntax_Syntax.lcomp_comp uu____6641))
in (FStar_Syntax_Util.comp_set_flags uu____6640 flags1))))))))))
end)))))
in (match ((not (should_return1))) with
| true -> begin
lc
end
| uu____6645 -> begin
(FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ flags1 refine1)
end)))))


let maybe_return_e2_and_bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r env e1opt lc1 e2 uu____6677 -> (match (uu____6677) with
| (x, lc2) -> begin
(

let lc21 = (

let eff1 = (FStar_TypeChecker_Env.norm_eff_name env lc1.FStar_Syntax_Syntax.eff_name)
in (

let eff2 = (FStar_TypeChecker_Env.norm_eff_name env lc2.FStar_Syntax_Syntax.eff_name)
in (

let uu____6689 = (((

let uu____6692 = (is_pure_or_ghost_effect env eff1)
in (not (uu____6692))) || (should_not_inline_lc lc1)) && (is_pure_or_ghost_effect env eff2))
in (match (uu____6689) with
| true -> begin
(maybe_assume_result_eq_pure_term env e2 lc2)
end
| uu____6693 -> begin
lc2
end))))
in (bind r env e1opt lc1 ((x), (lc21))))
end))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____6706 = (

let uu____6707 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____6707))
in (FStar_Syntax_Syntax.fvar uu____6706 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp)) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____6773 -> (match (uu____6773) with
| (uu____6786, eff_label, uu____6788, uu____6789) -> begin
(join_effects env eff eff_label)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let uu____6800 = (

let uu____6807 = (FStar_All.pipe_right lcases (FStar_Util.for_some (fun uu____6841 -> (match (uu____6841) with
| (uu____6854, uu____6855, flags1, uu____6857) -> begin
(FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___85_6871 -> (match (uu___85_6871) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____6872 -> begin
false
end))))
end))))
in (match (uu____6807) with
| true -> begin
((true), ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
end
| uu____6881 -> begin
((false), ([]))
end))
in (match (uu____6800) with
| (should_not_inline_whole_match, bind_cases_flags) -> begin
(

let bind_cases = (fun uu____6895 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____6897 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____6897) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____6898 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____6935 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____6936 = (

let uu____6941 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____6942 = (

let uu____6943 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____6950 = (

let uu____6959 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____6966 = (

let uu____6975 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____6982 = (

let uu____6991 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____6991)::[])
in (uu____6975)::uu____6982))
in (uu____6959)::uu____6966))
in (uu____6943)::uu____6950))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6941 uu____6942)))
in (uu____6936 FStar_Pervasives_Native.None uu____6935))))
in (

let default_case = (

let post_k = (

let uu____7034 = (

let uu____7041 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____7041)::[])
in (

let uu____7054 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____7034 uu____7054)))
in (

let kwp = (

let uu____7060 = (

let uu____7067 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____7067)::[])
in (

let uu____7080 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____7060 uu____7080)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____7087 = (

let uu____7088 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____7088)::[])
in (

let uu____7101 = (

let uu____7104 = (

let uu____7111 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____7111))
in (

let uu____7112 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____7104 uu____7112)))
in (FStar_Syntax_Util.abs uu____7087 uu____7101 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let maybe_return = (fun eff_label_then cthen -> (

let uu____7134 = (should_not_inline_whole_match || (

let uu____7136 = (is_pure_or_ghost_effect env eff)
in (not (uu____7136))))
in (match (uu____7134) with
| true -> begin
(cthen true)
end
| uu____7137 -> begin
(cthen false)
end)))
in (

let comp = (FStar_List.fold_right (fun uu____7169 celse -> (match (uu____7169) with
| (g, eff_label, uu____7185, cthen) -> begin
(

let uu____7197 = (

let uu____7222 = (

let uu____7223 = (maybe_return eff_label cthen)
in (FStar_Syntax_Syntax.lcomp_comp uu____7223))
in (lift_and_destruct env uu____7222 celse))
in (match (uu____7197) with
| ((md, uu____7225, uu____7226), (uu____7227, uu____7228, wp_then), (uu____7230, uu____7231, wp_else)) -> begin
(

let uu____7251 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____7251 []))
end))
end)) lcases default_case)
in (match (lcases) with
| [] -> begin
comp
end
| (uu____7265)::[] -> begin
comp
end
| uu____7305 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____7323 = (destruct_comp comp1)
in (match (uu____7323) with
| (uu____7330, uu____7331, wp) -> begin
(

let wp1 = (

let uu____7336 = (

let uu____7341 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____7342 = (

let uu____7343 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____7350 = (

let uu____7359 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____7359)::[])
in (uu____7343)::uu____7350))
in (FStar_Syntax_Syntax.mk_Tm_app uu____7341 uu____7342)))
in (uu____7336 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 bind_cases_flags))
end))))
end)))))
end))))
in (FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags bind_cases))
end))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____7418 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____7418) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7427 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____7432 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____7427 uu____7432)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____7475 = (

let uu____7476 = (FStar_Syntax_Subst.compress t2)
in uu____7476.FStar_Syntax_Syntax.n)
in (match (uu____7475) with
| FStar_Syntax_Syntax.Tm_type (uu____7479) -> begin
true
end
| uu____7480 -> begin
false
end))))
in (

let uu____7481 = (

let uu____7482 = (FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ)
in uu____7482.FStar_Syntax_Syntax.n)
in (match (uu____7481) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____7490 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (

let uu____7500 = (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____7500 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let lc1 = (

let uu____7502 = (

let uu____7503 = (

let uu____7504 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____7504))
in ((FStar_Pervasives_Native.None), (uu____7503)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____7502))
in (

let e1 = (

let uu____7510 = (

let uu____7515 = (

let uu____7516 = (FStar_Syntax_Syntax.as_arg e)
in (uu____7516)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7515))
in (uu____7510 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____7537 -> begin
((e), (lc))
end))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____7574 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____7574) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____7597 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____7619 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____7619), (false)))
end
| uu____7624 -> begin
(

let uu____7625 = (FStar_TypeChecker_Rel.get_subtyping_predicate env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____7625), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____7636) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____7645 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Errors.raise_error uu____7645 e.FStar_Syntax_Syntax.pos))
end
| uu____7656 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___113_7659 = lc
in {FStar_Syntax_Syntax.eff_name = uu___113_7659.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___113_7659.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___113_7659.FStar_Syntax_Syntax.comp_thunk})), (FStar_TypeChecker_Rel.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____7664 = (FStar_TypeChecker_Rel.guard_form g)
in (match (uu____7664) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc1 = (

let uu___114_7672 = lc
in {FStar_Syntax_Syntax.eff_name = uu___114_7672.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___114_7672.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___114_7672.FStar_Syntax_Syntax.comp_thunk})
in ((e), (lc1), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___115_7675 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___115_7675.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___115_7675.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___115_7675.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____7681 -> (

let uu____7682 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____7682) with
| true -> begin
(FStar_Syntax_Syntax.lcomp_comp lc)
end
| uu____7683 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in (

let uu____7685 = (

let uu____7686 = (FStar_Syntax_Subst.compress f1)
in uu____7686.FStar_Syntax_Syntax.n)
in (match (uu____7685) with
| FStar_Syntax_Syntax.Tm_abs (uu____7689, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7691; FStar_Syntax_Syntax.vars = uu____7692}, uu____7693) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___116_7715 = lc
in {FStar_Syntax_Syntax.eff_name = uu___116_7715.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___116_7715.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___116_7715.FStar_Syntax_Syntax.comp_thunk})
in (FStar_Syntax_Syntax.lcomp_comp lc1))
end
| uu____7716 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((

let uu____7719 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____7719) with
| true -> begin
(

let uu____7720 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____7721 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____7722 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____7723 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____7720 uu____7721 uu____7722 uu____7723)))))
end
| uu____7724 -> begin
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

let uu____7732 = (

let uu____7737 = (

let uu____7738 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____7738)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____7737))
in (uu____7732 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____7759 -> begin
f1
end)
in (

let uu____7760 = (

let uu____7765 = (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____7782 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____7783 = (FStar_Syntax_Util.lcomp_of_comp cret)
in (

let uu____7784 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____7765 uu____7782 e uu____7783 uu____7784)))))
in (match (uu____7760) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___117_7788 = x
in {FStar_Syntax_Syntax.ppname = uu___117_7788.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_7788.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____7790 = (FStar_Syntax_Util.lcomp_of_comp c)
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____7790 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((

let uu____7795 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____7795) with
| true -> begin
(

let uu____7796 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____7796))
end
| uu____7797 -> begin
()
end));
c2;
))))
end)))))));
))
end)))
end)))
in (

let flags1 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___86_7806 -> (match (uu___86_7806) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____7809 -> begin
[]
end))))
in (

let lc1 = (

let uu____7811 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____7811 t flags1 strengthen))
in (

let g2 = (

let uu___118_7813 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___118_7813.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___118_7813.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___118_7813.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end))))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____7848 = (

let uu____7851 = (

let uu____7856 = (

let uu____7857 = (

let uu____7864 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____7864))
in (uu____7857)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____7856))
in (uu____7851 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____7848))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in (

let uu____7885 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____7885) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____7894 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____7901) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____7916) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____7932 = ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))
in (match (uu____7932) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____7946))::((ens, uu____7948))::uu____7949 -> begin
(

let uu____7978 = (

let uu____7981 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____7981))
in (

let uu____7982 = (

let uu____7983 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____7983))
in ((uu____7978), (uu____7982))))
end
| uu____7986 -> begin
(

let uu____7995 = (

let uu____8000 = (

let uu____8001 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____8001))
in ((FStar_Errors.Fatal_EffectConstructorNotFullyApplied), (uu____8000)))
in (FStar_Errors.raise_error uu____7995 comp.FStar_Syntax_Syntax.pos))
end)
end
| uu____8008 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____8017))::uu____8018 -> begin
(

let uu____8037 = (

let uu____8042 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8042))
in (match (uu____8037) with
| (us_r, uu____8074) -> begin
(

let uu____8075 = (

let uu____8080 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8080))
in (match (uu____8075) with
| (us_e, uu____8112) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____8115 = (

let uu____8116 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar uu____8116 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8115 us_r))
in (

let as_ens = (

let uu____8118 = (

let uu____8119 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar uu____8119 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8118 us_e))
in (

let req = (

let uu____8123 = (

let uu____8128 = (

let uu____8129 = (

let uu____8138 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____8138)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____8129)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____8128))
in (uu____8123 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____8170 = (

let uu____8175 = (

let uu____8176 = (

let uu____8185 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____8185)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____8176)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____8175))
in (uu____8170 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____8214 = (

let uu____8217 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____8217))
in (

let uu____8218 = (

let uu____8219 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____8219))
in ((uu____8214), (uu____8218)))))))))
end))
end))
end
| uu____8222 -> begin
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

let uu____8252 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____8252) with
| true -> begin
(

let uu____8253 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____8254 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____8253 uu____8254)))
end
| uu____8255 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____8298 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____8298) with
| true -> begin
(

let uu____8299 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____8300 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____8299 uu____8300)))
end
| uu____8301 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____8307 = (

let uu____8308 = (

let uu____8309 = (FStar_Syntax_Subst.compress t)
in uu____8309.FStar_Syntax_Syntax.n)
in (match (uu____8308) with
| FStar_Syntax_Syntax.Tm_app (uu____8312) -> begin
false
end
| uu____8327 -> begin
true
end))
in (match (uu____8307) with
| true -> begin
t
end
| uu____8328 -> begin
(

let uu____8329 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____8329) with
| (head1, args) -> begin
(

let uu____8366 = (

let uu____8367 = (

let uu____8368 = (FStar_Syntax_Subst.compress head1)
in uu____8368.FStar_Syntax_Syntax.n)
in (match (uu____8367) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____8371 -> begin
false
end))
in (match (uu____8366) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____8393 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____8402 -> begin
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
| uu____8431 -> begin
(

let number_of_implicits = (fun t1 -> (

let uu____8438 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____8438) with
| (formals, uu____8452) -> begin
(

let n_implicits = (

let uu____8470 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____8548 -> (match (uu____8548) with
| (uu____8555, imp) -> begin
((Prims.op_Equality imp FStar_Pervasives_Native.None) || (Prims.op_Equality imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality))))
end))))
in (match (uu____8470) with
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

let uu____8688 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____8688) with
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

let uu____8712 = (

let uu____8717 = (

let uu____8718 = (FStar_Util.string_of_int n_expected)
in (

let uu____8725 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____8726 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____8718 uu____8725 uu____8726))))
in ((FStar_Errors.Fatal_MissingImplicitArguments), (uu____8717)))
in (

let uu____8733 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____8712 uu____8733)))
end
| uu____8736 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___87_8756 -> (match (uu___87_8756) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____8786 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____8786) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_18), uu____8901) when (_0_18 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end
| (uu____8944, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t1 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____8977 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t1)
in (match (uu____8977) with
| (v1, uu____9017, g) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____9036 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____9036) with
| (args, bs3, subst3, g') -> begin
(

let uu____9129 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs3), (subst3), (uu____9129)))
end)))
end)))
end
| (uu____9156, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let uu____9202 = (

let uu____9229 = (inst_n_binders t)
in (aux [] uu____9229 bs1))
in (match (uu____9202) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____9300) -> begin
((e), (torig), (guard))
end
| (uu____9331, []) when (

let uu____9362 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____9362))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| uu____9363 -> begin
(

let t1 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____9391 -> begin
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
| uu____9404 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____9414 = (

let uu____9417 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____9417 (FStar_List.map (fun u -> (

let uu____9427 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____9427 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____9414 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____9448 = (FStar_Util.set_is_empty x)
in (match (uu____9448) with
| true -> begin
[]
end
| uu____9451 -> begin
(

let s = (

let uu____9463 = (

let uu____9474 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____9474))
in (FStar_All.pipe_right uu____9463 FStar_Util.set_elements))
in ((

let uu____9506 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9506) with
| true -> begin
(

let uu____9507 = (

let uu____9508 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____9508))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____9507))
end
| uu____9511 -> begin
()
end));
(

let r = (

let uu____9515 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____9515))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____9554 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9554) with
| true -> begin
(

let uu____9555 = (

let uu____9556 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____9556))
in (

let uu____9557 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____9558 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____9555 uu____9557 uu____9558))))
end
| uu____9559 -> begin
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

let uu____9584 = (FStar_Util.set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____9584 FStar_Util.set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____9622) -> begin
generalized_univ_names
end
| (uu____9629, []) -> begin
explicit_univ_names
end
| uu____9636 -> begin
(

let uu____9645 = (

let uu____9650 = (

let uu____9651 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____9651))
in ((FStar_Errors.Fatal_UnexpectedGeneralizedUniverse), (uu____9650)))
in (FStar_Errors.raise_error uu____9645 t.FStar_Syntax_Syntax.pos))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in ((

let uu____9669 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9669) with
| true -> begin
(

let uu____9670 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____9671 = (FStar_Syntax_Print.univ_names_to_string univnames1)
in (FStar_Util.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" uu____9670 uu____9671)))
end
| uu____9672 -> begin
()
end));
(

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____9677 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9677) with
| true -> begin
(

let uu____9678 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____9678))
end
| uu____9679 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____9684 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9684) with
| true -> begin
(

let uu____9685 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____9686 = (FStar_Syntax_Print.univ_names_to_string gen1)
in (FStar_Util.print2 "After generalization, t: %s and univs: %s\n" uu____9685 uu____9686)))
end
| uu____9687 -> begin
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

let uu____9764 = (

let uu____9765 = (FStar_Util.for_all (fun uu____9778 -> (match (uu____9778) with
| (uu____9787, uu____9788, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____9765))
in (match (uu____9764) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9828 -> begin
(

let norm1 = (fun c -> ((

let uu____9836 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____9836) with
| true -> begin
(

let uu____9837 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____9837))
end
| uu____9838 -> begin
()
end));
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env c)
in ((

let uu____9841 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____9841) with
| true -> begin
(

let uu____9842 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____9842))
end
| uu____9843 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____9857 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____9857 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____9893 -> (match (uu____9893) with
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

let uu____9937 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____9937) with
| true -> begin
(

let uu____9938 = (

let uu____9939 = (

let uu____9942 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____9942 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____9939 (FStar_String.concat ", ")))
in (

let uu____9985 = (

let uu____9986 = (

let uu____9989 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____9989 (FStar_List.map (fun u -> (

let uu____10000 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____10001 = (FStar_Syntax_Print.term_to_string u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____10000 uu____10001)))))))
in (FStar_All.pipe_right uu____9986 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9938 uu____9985)))
end
| uu____10004 -> begin
()
end));
(

let univs2 = (

let uu____10008 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uv -> (

let uu____10020 = (FStar_Syntax_Free.univs uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.set_union univs2 uu____10020))) univs1 uu____10008))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____10027 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____10027) with
| true -> begin
(

let uu____10028 = (

let uu____10029 = (

let uu____10032 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____10032 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____10029 (FStar_String.concat ", ")))
in (

let uu____10075 = (

let uu____10076 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> (

let uu____10087 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____10088 = (FStar_TypeChecker_Normalize.term_to_string env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____10087 uu____10088))))))
in (FStar_All.pipe_right uu____10076 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____10028 uu____10075)))
end
| uu____10091 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
))))))
end))
in (

let uu____10102 = (

let uu____10119 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____10119))
in (match (uu____10102) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____10211 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____10211) with
| true -> begin
()
end
| uu____10212 -> begin
(

let uu____10213 = lec_hd
in (match (uu____10213) with
| (lb1, uu____10221, uu____10222) -> begin
(

let uu____10223 = lec2
in (match (uu____10223) with
| (lb2, uu____10231, uu____10232) -> begin
(

let msg = (

let uu____10234 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____10235 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____10234 uu____10235)))
in (

let uu____10236 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleSetOfUniverse), (msg)) uu____10236)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun u -> (FStar_All.pipe_right u21 (FStar_Util.for_some (fun u' -> (FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head u'.FStar_Syntax_Syntax.ctx_uvar_head))))))))
in (

let uu____10300 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____10300) with
| true -> begin
()
end
| uu____10301 -> begin
(

let uu____10302 = lec_hd
in (match (uu____10302) with
| (lb1, uu____10310, uu____10311) -> begin
(

let uu____10312 = lec2
in (match (uu____10312) with
| (lb2, uu____10320, uu____10321) -> begin
(

let msg = (

let uu____10323 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____10324 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____10323 uu____10324)))
in (

let uu____10325 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleNumberOfTypes), (msg)) uu____10325)))
end))
end))
end))))
in (

let lecs1 = (

let uu____10335 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____10394 = (univs_and_uvars_of_lec this_lec)
in (match (uu____10394) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____10335 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail1 = (fun k -> (

let uu____10495 = lec_hd
in (match (uu____10495) with
| (lbname, e, c) -> begin
(

let uu____10505 = (

let uu____10510 = (

let uu____10511 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____10512 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____10513 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____10511 uu____10512 uu____10513))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____10510)))
in (

let uu____10514 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____10505 uu____10514)))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun u -> (

let uu____10535 = (FStar_Syntax_Unionfind.find u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____10535) with
| FStar_Pervasives_Native.Some (uu____10544) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____10551 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____10555 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____10555) with
| (bs, kres) -> begin
((

let uu____10593 = (

let uu____10594 = (

let uu____10597 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____10597))
in uu____10594.FStar_Syntax_Syntax.n)
in (match (uu____10593) with
| FStar_Syntax_Syntax.Tm_type (uu____10598) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____10602 = (

let uu____10603 = (FStar_Util.set_is_empty free)
in (not (uu____10603)))
in (match (uu____10602) with
| true -> begin
(fail1 kres)
end
| uu____10604 -> begin
()
end)))
end
| uu____10605 -> begin
(fail1 kres)
end));
(

let a = (

let uu____10607 = (

let uu____10610 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) uu____10610))
in (FStar_Syntax_Syntax.new_bv uu____10607 kres))
in (

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Syntax.bv_to_name a)
end
| uu____10618 -> begin
(

let uu____10625 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____10625 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
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

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____10736 -> (match (uu____10736) with
| (lbname, e, c) -> begin
(

let uu____10790 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____10865 -> begin
(

let uu____10880 = ((e), (c))
in (match (uu____10880) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____10931 -> (match (uu____10931) with
| (x, uu____10939) -> begin
(

let uu____10944 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____10944))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____10962 = (

let uu____10963 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____10963))
in (match (uu____10962) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____10966 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____10967 -> begin
e1
end)
in (

let t = (

let uu____10969 = (

let uu____10970 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____10970.FStar_Syntax_Syntax.n)
in (match (uu____10969) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____10991 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____10991) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____11004 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____11008 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____11008), (gen_tvars))))))))
end))
end)
in (match (uu____10790) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____11162 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____11162) with
| true -> begin
(

let uu____11163 = (

let uu____11164 = (FStar_List.map (fun uu____11177 -> (match (uu____11177) with
| (lb, uu____11185, uu____11186) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____11164 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____11163))
end
| uu____11189 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____11207 -> (match (uu____11207) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____11236 = (gen env is_rec lecs)
in (match (uu____11236) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____11335 -> (match (uu____11335) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____11397 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____11397) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____11443 -> (match (uu____11443) with
| (l, us, e, c, gvs) -> begin
(

let uu____11477 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____11478 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____11479 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____11480 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11481 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____11477 uu____11478 uu____11479 uu____11480 uu____11481))))))
end))))
end
| uu____11482 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____11522 -> (match (uu____11522) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____11566 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____11566), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check1 = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____11622 -> begin
(

let uu____11623 = (FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21)
in (match (uu____11623) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____11629 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) uu____11629))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____11638 = (

let uu____11639 = (FStar_Syntax_Subst.compress e1)
in uu____11639.FStar_Syntax_Syntax.n)
in (match (uu____11638) with
| FStar_Syntax_Syntax.Tm_name (uu____11642) -> begin
true
end
| uu____11643 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___119_11663 = x
in {FStar_Syntax_Syntax.ppname = uu___119_11663.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_11663.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____11664 -> begin
e2
end)))
in (

let env2 = (

let uu___120_11666 = env1
in (

let uu____11667 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___120_11666.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___120_11666.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___120_11666.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___120_11666.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___120_11666.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___120_11666.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___120_11666.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___120_11666.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___120_11666.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___120_11666.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___120_11666.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___120_11666.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___120_11666.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___120_11666.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___120_11666.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___120_11666.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____11667; FStar_TypeChecker_Env.is_iface = uu___120_11666.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___120_11666.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___120_11666.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___120_11666.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___120_11666.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___120_11666.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___120_11666.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___120_11666.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___120_11666.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___120_11666.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___120_11666.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___120_11666.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___120_11666.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___120_11666.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___120_11666.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___120_11666.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___120_11666.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___120_11666.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___120_11666.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___120_11666.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___120_11666.FStar_TypeChecker_Env.dep_graph}))
in (

let uu____11668 = (check1 env2 t1 t2)
in (match (uu____11668) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11675 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____11680 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____11675 uu____11680)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____11687 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____11687) with
| true -> begin
(

let uu____11688 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____11688))
end
| uu____11689 -> begin
()
end));
(

let uu____11690 = (decorate e t2)
in ((uu____11690), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____11722 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____11722) with
| true -> begin
(

let uu____11727 = (discharge g1)
in (

let uu____11728 = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((uu____11727), (uu____11728))))
end
| uu____11729 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]
in (

let c1 = (

let uu____11735 = (

let uu____11736 = (

let uu____11737 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____11737 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____11736 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____11735 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11739 = (destruct_comp c1)
in (match (uu____11739) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____11756 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____11757 = (

let uu____11762 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____11763 = (

let uu____11764 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____11771 = (

let uu____11780 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____11780)::[])
in (uu____11764)::uu____11771))
in (FStar_Syntax_Syntax.mk_Tm_app uu____11762 uu____11763)))
in (uu____11757 FStar_Pervasives_Native.None uu____11756)))
in ((

let uu____11808 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____11808) with
| true -> begin
(

let uu____11809 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____11809))
end
| uu____11810 -> begin
()
end));
(

let g2 = (

let uu____11812 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g1 uu____11812))
in (

let uu____11813 = (discharge g2)
in (

let uu____11814 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____11813), (uu____11814)))));
))
end))))))
end)))))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___88_11846 -> (match (uu___88_11846) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____11854))::[] -> begin
(f fst1)
end
| uu____11871 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____11882 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____11882 (fun _0_21 -> FStar_TypeChecker_Common.NonTrivial (_0_21)))))
in (

let op_or_e = (fun e -> (

let uu____11893 = (

let uu____11894 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____11894))
in (FStar_All.pipe_right uu____11893 (fun _0_22 -> FStar_TypeChecker_Common.NonTrivial (_0_22)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_23 -> FStar_TypeChecker_Common.NonTrivial (_0_23))))
in (

let op_or_t = (fun t -> (

let uu____11913 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____11913 (fun _0_24 -> FStar_TypeChecker_Common.NonTrivial (_0_24)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_25 -> FStar_TypeChecker_Common.NonTrivial (_0_25))))
in (

let short_op_ite = (fun uu___89_11927 -> (match (uu___89_11927) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____11935))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____11954))::[] -> begin
(

let uu____11983 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____11983 (fun _0_26 -> FStar_TypeChecker_Common.NonTrivial (_0_26))))
end
| uu____11984 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____11995 = (

let uu____12003 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____12003)))
in (

let uu____12011 = (

let uu____12021 = (

let uu____12029 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____12029)))
in (

let uu____12037 = (

let uu____12047 = (

let uu____12055 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____12055)))
in (

let uu____12063 = (

let uu____12073 = (

let uu____12081 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____12081)))
in (

let uu____12089 = (

let uu____12099 = (

let uu____12107 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____12107)))
in (uu____12099)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____12073)::uu____12089))
in (uu____12047)::uu____12063))
in (uu____12021)::uu____12037))
in (uu____11995)::uu____12011))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____12169 = (FStar_Util.find_map table (fun uu____12184 -> (match (uu____12184) with
| (x, mk1) -> begin
(

let uu____12201 = (FStar_Ident.lid_equals x lid)
in (match (uu____12201) with
| true -> begin
(

let uu____12204 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____12204))
end
| uu____12205 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (uu____12169) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____12207 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____12213 = (

let uu____12214 = (FStar_Syntax_Util.un_uinst l)
in uu____12214.FStar_Syntax_Syntax.n)
in (match (uu____12213) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____12218 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____12248))::uu____12249 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____12260 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____12267, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____12268))))::uu____12269 -> begin
bs
end
| uu____12280 -> begin
(

let uu____12281 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____12281) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____12285 = (

let uu____12286 = (FStar_Syntax_Subst.compress t)
in uu____12286.FStar_Syntax_Syntax.n)
in (match (uu____12285) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____12290) -> begin
(

let uu____12307 = (FStar_Util.prefix_until (fun uu___90_12347 -> (match (uu___90_12347) with
| (uu____12354, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____12355))) -> begin
false
end
| uu____12358 -> begin
true
end)) bs')
in (match (uu____12307) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____12393, uu____12394) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____12466, uu____12467) -> begin
(

let uu____12540 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____12558 -> (match (uu____12558) with
| (x, uu____12566) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____12540) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____12609 -> (match (uu____12609) with
| (x, i) -> begin
(

let uu____12628 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____12628), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____12635 -> begin
bs
end))
end))
end
| uu____12636 -> begin
bs
end))
end))
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 t -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in (

let uu____12664 = (((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1)))
in (match (uu____12664) with
| true -> begin
e
end
| uu____12665 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end)))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____12691 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____12691) with
| true -> begin
e
end
| uu____12692 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____12726 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____12726) with
| true -> begin
((

let uu____12728 = (FStar_Ident.text_of_lid lident)
in (d uu____12728));
(

let uu____12729 = (FStar_Ident.text_of_lid lident)
in (

let uu____12730 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" uu____12729 uu____12730)));
)
end
| uu____12731 -> begin
()
end));
(

let fv = (

let uu____12733 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____12733 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (((FStar_Syntax_Util.mk_letbinding lbname [] FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def [] FStar_Range.dummyRange))::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____12743 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___121_12745 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___121_12745.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___121_12745.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___121_12745.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___121_12745.FStar_Syntax_Syntax.sigattrs})), (uu____12743)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (

let visibility = (fun uu___91_12761 -> (match (uu___91_12761) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____12762 -> begin
false
end))
in (

let reducibility = (fun uu___92_12768 -> (match (uu___92_12768) with
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
| uu____12769 -> begin
false
end))
in (

let assumption = (fun uu___93_12775 -> (match (uu___93_12775) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____12776 -> begin
false
end))
in (

let reification = (fun uu___94_12782 -> (match (uu___94_12782) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____12783) -> begin
true
end
| uu____12784 -> begin
false
end))
in (

let inferred = (fun uu___95_12790 -> (match (uu___95_12790) with
| FStar_Syntax_Syntax.Discriminator (uu____12791) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____12792) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____12797) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____12806) -> begin
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
| uu____12815 -> begin
false
end))
in (

let has_eq = (fun uu___96_12821 -> (match (uu___96_12821) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____12822 -> begin
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
| FStar_Syntax_Syntax.Reflectable (uu____12886) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____12891 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let uu____12895 = (

let uu____12896 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___97_12900 -> (match (uu___97_12900) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____12901 -> begin
false
end))))
in (FStar_All.pipe_right uu____12896 Prims.op_Negation))
in (match (uu____12895) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____12916 = (

let uu____12921 = (

let uu____12922 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____12922 msg))
in ((FStar_Errors.Fatal_QulifierListNotPermitted), (uu____12921)))
in (FStar_Errors.raise_error uu____12916 r)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____12934 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____12936 -> begin
()
end);
(

let uu____12938 = (

let uu____12939 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____12939)))
in (match (uu____12938) with
| true -> begin
(err "ill-formed combination")
end
| uu____12942 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____12944), uu____12945) -> begin
((

let uu____12955 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____12955) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____12958 -> begin
()
end));
(

let uu____12959 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____12959) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____12964 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____12965) -> begin
(

let uu____12974 = (

let uu____12975 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____12975)))
in (match (uu____12974) with
| true -> begin
(err'1 ())
end
| uu____12980 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____12981) -> begin
(

let uu____12988 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____12988) with
| true -> begin
(err'1 ())
end
| uu____12991 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____12992) -> begin
(

let uu____12999 = (

let uu____13000 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____13000)))
in (match (uu____12999) with
| true -> begin
(err'1 ())
end
| uu____13005 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____13006) -> begin
(

let uu____13007 = (

let uu____13008 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____13008)))
in (match (uu____13007) with
| true -> begin
(err'1 ())
end
| uu____13013 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____13014) -> begin
(

let uu____13015 = (

let uu____13016 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____13016)))
in (match (uu____13015) with
| true -> begin
(err'1 ())
end
| uu____13021 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____13022) -> begin
(

let uu____13035 = (

let uu____13036 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____13036)))
in (match (uu____13035) with
| true -> begin
(err'1 ())
end
| uu____13041 -> begin
()
end))
end
| uu____13042 -> begin
()
end);
))))))
end
| uu____13043 -> begin
()
end)))))))))))


let must_erase_for_extraction : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun g t -> (

let rec aux_whnf = (fun env t1 -> (

let uu____13076 = (

let uu____13077 = (FStar_Syntax_Subst.compress t1)
in uu____13077.FStar_Syntax_Syntax.n)
in (match (uu____13076) with
| FStar_Syntax_Syntax.Tm_type (uu____13080) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (

let uu____13083 = (

let uu____13088 = (FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv)
in (FStar_All.pipe_right uu____13088 (FStar_TypeChecker_Env.lookup_attrs_of_lid g)))
in (FStar_All.pipe_right uu____13083 (fun l_opt -> ((FStar_Util.is_some l_opt) && (

let uu____13106 = (FStar_All.pipe_right l_opt FStar_Util.must)
in (FStar_All.pipe_right uu____13106 (FStar_List.existsb (fun t2 -> (

let uu____13123 = (

let uu____13124 = (FStar_Syntax_Subst.compress t2)
in uu____13124.FStar_Syntax_Syntax.n)
in (match (uu____13123) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_Ident.lid_equals fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.must_erase_for_extraction_attr) -> begin
true
end
| uu____13128 -> begin
false
end)))))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____13129) -> begin
(

let uu____13142 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____13142) with
| (bs, c) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____13168 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____13168) with
| true -> begin
(aux env1 (FStar_Syntax_Util.comp_result c))
end
| uu____13169 -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____13170; FStar_Syntax_Syntax.index = uu____13171; FStar_Syntax_Syntax.sort = t2}, uu____13173) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____13181, uu____13182) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____13224)::[]) -> begin
(

let uu____13255 = (

let uu____13256 = (FStar_Syntax_Util.un_uinst head1)
in uu____13256.FStar_Syntax_Syntax.n)
in (match (uu____13255) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
end
| uu____13260 -> begin
false
end))
end
| uu____13261 -> begin
false
end)))
and aux = (fun env t1 -> (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Iota)::[]) env t1)
in (

let res = (aux_whnf env t2)
in ((

let uu____13269 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Extraction")))
in (match (uu____13269) with
| true -> begin
(

let uu____13270 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "must_erase=%s: %s\n" (match (res) with
| true -> begin
"true"
end
| uu____13271 -> begin
"false"
end) uu____13270))
end
| uu____13272 -> begin
()
end));
res;
))))
in (aux g t)))




