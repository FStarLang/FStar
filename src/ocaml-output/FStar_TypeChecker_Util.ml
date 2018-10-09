
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  unit = (fun env errs -> (

let uu____21 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____22 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.log_issue uu____21 uu____22))))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (FStar_TypeChecker_Env.new_implicit_var_aux reason r env k FStar_Syntax_Syntax.Strict))


let close_guard_implicits : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env xs g -> (

let uu____74 = (

let uu____75 = (FStar_Options.eager_subtyping ())
in (FStar_All.pipe_left Prims.op_Negation uu____75))
in (match (uu____74) with
| true -> begin
g
end
| uu____76 -> begin
(

let uu____77 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred (FStar_List.partition (fun uu____123 -> (match (uu____123) with
| (uu____128, p) -> begin
(FStar_TypeChecker_Rel.flex_prob_closing env xs p)
end))))
in (match (uu____77) with
| (solve_now, defer) -> begin
((

let uu____157 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____157) with
| true -> begin
((FStar_Util.print_string "SOLVE BEFORE CLOSING:\n");
(FStar_List.iter (fun uu____168 -> (match (uu____168) with
| (s, p) -> begin
(

let uu____175 = (FStar_TypeChecker_Rel.prob_to_string env p)
in (FStar_Util.print2 "%s: %s\n" s uu____175))
end)) solve_now);
(FStar_Util.print_string " ...DEFERRED THE REST:\n");
(FStar_List.iter (fun uu____186 -> (match (uu____186) with
| (s, p) -> begin
(

let uu____193 = (FStar_TypeChecker_Rel.prob_to_string env p)
in (FStar_Util.print2 "%s: %s\n" s uu____193))
end)) defer);
(FStar_Util.print_string "END\n");
)
end
| uu____194 -> begin
()
end));
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env (

let uu___358_197 = g
in {FStar_TypeChecker_Env.guard_f = uu___358_197.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = solve_now; FStar_TypeChecker_Env.univ_ineqs = uu___358_197.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___358_197.FStar_TypeChecker_Env.implicits}))
in (

let g2 = (

let uu___359_199 = g1
in {FStar_TypeChecker_Env.guard_f = uu___359_199.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = defer; FStar_TypeChecker_Env.univ_ineqs = uu___359_199.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___359_199.FStar_TypeChecker_Env.implicits})
in g2));
)
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____213 = (

let uu____214 = (FStar_Util.set_is_empty uvs)
in (not (uu____214)))
in (match (uu____213) with
| true -> begin
(

let us = (

let uu____216 = (

let uu____219 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun u -> (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)) uu____219))
in (FStar_All.pipe_right uu____216 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____230 = (

let uu____235 = (

let uu____236 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____236))
in ((FStar_Errors.Error_UncontrainedUnificationVar), (uu____235)))
in (FStar_Errors.log_issue r uu____230));
(FStar_Options.pop ());
))
end
| uu____237 -> begin
()
end))))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____253 -> (match (uu____253) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____263; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____265; FStar_Syntax_Syntax.lbpos = uu____266} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____299 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 e)
in (match (uu____299) with
| (univ_vars2, e1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars2)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let rec aux = (fun e2 -> (

let e3 = (FStar_Syntax_Subst.compress e2)
in (match (e3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e4, uu____336) -> begin
(aux e4)
end
| FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____343) -> begin
(FStar_Pervasives_Native.fst t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____398) -> begin
(

let res = (aux body)
in (

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____434 = (FStar_Options.ml_ish ())
in (match (uu____434) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____437 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in ((

let uu____453 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____453) with
| true -> begin
(

let uu____454 = (FStar_Range.string_of_range r)
in (

let uu____455 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Using type %s\n" uu____454 uu____455)))
end
| uu____456 -> begin
()
end));
FStar_Util.Inl (t2);
))))
end
| uu____457 -> begin
FStar_Util.Inl (FStar_Syntax_Syntax.tun)
end)))
in (

let t2 = (

let uu____459 = (aux e1)
in (match (uu____459) with
| FStar_Util.Inr (c) -> begin
(

let uu____465 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____465) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____466 -> begin
(

let uu____467 = (

let uu____472 = (

let uu____473 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____473))
in ((FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec), (uu____472)))
in (FStar_Errors.raise_error uu____467 rng))
end))
end
| FStar_Util.Inl (t2) -> begin
t2
end))
in ((univ_vars2), (t2), (true))))))
end))
end
| uu____477 -> begin
(

let uu____478 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____478) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____537 -> (match (uu____537) with
| (p, i) -> begin
(

let uu____554 = (decorated_pattern_as_term p)
in (match (uu____554) with
| (vars, te) -> begin
(

let uu____577 = (

let uu____582 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____582)))
in ((vars), (uu____577)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____596 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____596)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____600 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____600)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____604 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____604)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____625 = (

let uu____644 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____644 FStar_List.unzip))
in (match (uu____625) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____780 = (

let uu____781 = (

let uu____782 = (

let uu____799 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____799), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____782))
in (mk1 uu____781))
in ((vars1), (uu____780))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let comp_univ_opt : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____837, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.GTotal (uu____847, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::uu____861 -> begin
FStar_Pervasives_Native.Some (hd1)
end)
end))


let lcomp_univ_opt : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun lc -> (

let uu____871 = (FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp)
in (FStar_All.pipe_right uu____871 comp_univ_opt)))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____899))::[] -> begin
wp
end
| uu____924 -> begin
(

let uu____935 = (

let uu____936 = (

let uu____937 = (FStar_List.map (fun uu____949 -> (match (uu____949) with
| (x, uu____957) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____937 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____936))
in (failwith uu____935))
end)
in (

let uu____964 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____964), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____980 = (destruct_comp c)
in (match (uu____980) with
| (u, uu____988, wp) -> begin
(

let uu____990 = (

let uu____1001 = (

let uu____1010 = (lift.FStar_TypeChecker_Env.mlift_wp u c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____1010))
in (uu____1001)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____990; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____1042 = (

let uu____1049 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____1050 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____1049 uu____1050)))
in (match (uu____1042) with
| (m, uu____1052, uu____1053) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____1069 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____1069) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____1070 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____1112 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____1112) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____1149 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____1149) with
| (a, kwp) -> begin
(

let uu____1180 = (destruct_comp m1)
in (

let uu____1187 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____1180), (uu____1187))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags1 -> (

let uu____1267 = (

let uu____1268 = (

let uu____1279 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1279)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____1268; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp uu____1267)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags1 -> (

let uu____1361 = (FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)
in (match (uu____1361) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____1362 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1)
end)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu____1373 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____1373 lc.FStar_Syntax_Syntax.cflags (fun uu____1376 -> (

let uu____1377 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Subst.subst_comp subst1 uu____1377))))))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1383 = (

let uu____1384 = (FStar_Syntax_Subst.compress t)
in uu____1384.FStar_Syntax_Syntax.n)
in (match (uu____1383) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1387) -> begin
true
end
| uu____1402 -> begin
false
end)))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (reason1) -> begin
(

let uu____1459 = (

let uu____1460 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____1460))
in (match (uu____1459) with
| true -> begin
f
end
| uu____1461 -> begin
(

let uu____1462 = (reason1 ())
in (label uu____1462 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___360_1479 = g
in (

let uu____1480 = (

let uu____1481 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____1481))
in {FStar_TypeChecker_Env.guard_f = uu____1480; FStar_TypeChecker_Env.deferred = uu___360_1479.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___360_1479.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___360_1479.FStar_TypeChecker_Env.implicits}))
end))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____1501 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____1501) with
| true -> begin
c
end
| uu____1502 -> begin
(

let uu____1503 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____1503) with
| true -> begin
c
end
| uu____1504 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____1564 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1564)::[])
in (

let us = (

let uu____1586 = (

let uu____1589 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____1589)::[])
in (u_res)::uu____1586)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____1595 = (

let uu____1600 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____1601 = (

let uu____1602 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____1611 = (

let uu____1622 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____1631 = (

let uu____1642 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____1642)::[])
in (uu____1622)::uu____1631))
in (uu____1602)::uu____1611))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1600 uu____1601)))
in (uu____1595 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____1686 = (destruct_comp c1)
in (match (uu____1686) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end)))


let close_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____1721 -> (

let uu____1722 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (close_comp env bvs uu____1722)))))


let should_not_inline_lc : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___340_1731 -> (match (uu___340_1731) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____1732 -> begin
false
end)))))


let should_return : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun env eopt lc -> (match (eopt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (e) -> begin
((((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) && (

let uu____1754 = (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ)
in (not (uu____1754)))) && (

let uu____1761 = (FStar_Syntax_Util.head_and_args' e)
in (match (uu____1761) with
| (head1, uu____1777) -> begin
(

let uu____1798 = (

let uu____1799 = (FStar_Syntax_Util.un_uinst head1)
in uu____1799.FStar_Syntax_Syntax.n)
in (match (uu____1798) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____1803 = (

let uu____1804 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_irreducible env uu____1804))
in (not (uu____1803)))
end
| uu____1805 -> begin
true
end))
end))) && (

let uu____1807 = (should_not_inline_lc lc)
in (not (uu____1807))))
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env u_t_opt t v1 -> (

let c = (

let uu____1833 = (

let uu____1834 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____1834))
in (match (uu____1833) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____1835 -> begin
(

let uu____1836 = (FStar_Syntax_Util.is_unit t)
in (match (uu____1836) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero)))
end
| uu____1837 -> begin
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

let uu____1842 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____1842) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____1843 -> begin
(

let uu____1844 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____1844) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____1854 = (

let uu____1855 = (

let uu____1860 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____1861 = (

let uu____1862 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____1871 = (

let uu____1882 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____1882)::[])
in (uu____1862)::uu____1871))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1860 uu____1861)))
in (uu____1855 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::[]) env uu____1854)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
end))
in ((

let uu____1918 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____1918) with
| true -> begin
(

let uu____1919 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____1920 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____1921 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____1919 uu____1920 uu____1921))))
end
| uu____1922 -> begin
()
end));
c;
)))


let weaken_flags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags1 -> (

let uu____1934 = (FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___341_1938 -> (match (uu___341_1938) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____1939 -> begin
false
end))))
in (match (uu____1934) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____1942 -> begin
(FStar_All.pipe_right flags1 (FStar_List.collect (fun uu___342_1948 -> (match (uu___342_1948) with
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

let uu____1967 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____1967) with
| true -> begin
c
end
| uu____1968 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____1970 = (destruct_comp c1)
in (match (uu____1970) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____1984 = (

let uu____1989 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____1990 = (

let uu____1991 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____2000 = (

let uu____2011 = (FStar_Syntax_Syntax.as_arg formula)
in (

let uu____2020 = (

let uu____2031 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2031)::[])
in (uu____2011)::uu____2020))
in (uu____1991)::uu____2000))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1989 uu____1990)))
in (uu____1984 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (

let uu____2074 = (weaken_flags c1.FStar_Syntax_Syntax.flags)
in (mk_comp md u_res_t res_t wp1 uu____2074))))
end)))
end)))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____2097 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let uu____2099 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2099) with
| true -> begin
c
end
| uu____2100 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(weaken_comp env c f1)
end)
end))))
in (

let uu____2102 = (weaken_flags lc.FStar_Syntax_Syntax.cflags)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ uu____2102 weaken))))


let strengthen_comp : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun env reason c f flags1 -> (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____2143 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____2145 = (destruct_comp c1)
in (match (uu____2145) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____2159 = (

let uu____2164 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____2165 = (

let uu____2166 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____2175 = (

let uu____2186 = (

let uu____2195 = (

let uu____2196 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____2196 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2195))
in (

let uu____2205 = (

let uu____2216 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2216)::[])
in (uu____2186)::uu____2205))
in (uu____2166)::uu____2175))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2164 uu____2165)))
in (uu____2159 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 flags1)))
end)))
end))


let strengthen_precondition : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e_for_debugging_only lc g0 -> (

let uu____2301 = (FStar_TypeChecker_Env.is_trivial_guard_formula g0)
in (match (uu____2301) with
| true -> begin
((lc), (g0))
end
| uu____2306 -> begin
(

let flags1 = (

let uu____2310 = (

let uu____2317 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____2317) with
| true -> begin
((true), ((FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]))
end
| uu____2326 -> begin
((false), ([]))
end))
in (match (uu____2310) with
| (maybe_trivial_post, flags1) -> begin
(

let uu____2337 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___343_2345 -> (match (uu___343_2345) with
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
| uu____2348 -> begin
[]
end))))
in (FStar_List.append flags1 uu____2337))
end))
in (

let strengthen = (fun uu____2354 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____2356 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____2358 = (FStar_TypeChecker_Env.guard_form g01)
in (match (uu____2358) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____2361 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____2361) with
| true -> begin
(

let uu____2362 = (FStar_TypeChecker_Normalize.term_to_string env e_for_debugging_only)
in (

let uu____2363 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____2362 uu____2363)))
end
| uu____2364 -> begin
()
end));
(strengthen_comp env reason c f flags1);
)
end)))
end)))
in (

let uu____2365 = (

let uu____2366 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____2366 lc.FStar_Syntax_Syntax.res_typ flags1 strengthen))
in ((uu____2365), ((

let uu___361_2368 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___361_2368.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___361_2368.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___361_2368.FStar_TypeChecker_Env.implicits}))))))
end)))


let lcomp_has_trivial_postcondition : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) || (FStar_Util.for_some (fun uu___344_2375 -> (match (uu___344_2375) with
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
true
end
| uu____2376 -> begin
false
end)) lc.FStar_Syntax_Syntax.cflags)))


let maybe_add_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env uopt lc e -> (

let uu____2403 = ((FStar_Syntax_Util.is_lcomp_partial_return lc) || env.FStar_TypeChecker_Env.lax)
in (match (uu____2403) with
| true -> begin
e
end
| uu____2406 -> begin
(

let uu____2407 = ((lcomp_has_trivial_postcondition lc) && (

let uu____2409 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____2409)))
in (match (uu____2407) with
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
| uu____2432 -> begin
e
end))
end)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____2459 -> (match (uu____2459) with
| (b, lc2) -> begin
(

let debug1 = (fun f -> (

let uu____2479 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____2479) with
| true -> begin
(f ())
end
| uu____2480 -> begin
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

let uu____2487 = ((should_not_inline_lc lc11) || (should_not_inline_lc lc21))
in (match (uu____2487) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____2490 -> begin
(

let flags1 = (

let uu____2494 = (FStar_Syntax_Util.is_total_lcomp lc11)
in (match (uu____2494) with
| true -> begin
(

let uu____2497 = (FStar_Syntax_Util.is_total_lcomp lc21)
in (match (uu____2497) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____2500 -> begin
(

let uu____2501 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
in (match (uu____2501) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____2504 -> begin
[]
end))
end))
end
| uu____2505 -> begin
(

let uu____2506 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) && (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21))
in (match (uu____2506) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____2509 -> begin
[]
end))
end))
in (

let uu____2510 = (lcomp_has_trivial_postcondition lc21)
in (match (uu____2510) with
| true -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::flags1
end
| uu____2513 -> begin
flags1
end)))
end))
in (

let bind_it = (fun uu____2519 -> (

let uu____2520 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2520) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____2522 -> begin
(

let c1 = (FStar_Syntax_Syntax.lcomp_comp lc11)
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp lc21)
in ((debug1 (fun uu____2534 -> (

let uu____2535 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____2536 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____2538 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n" uu____2535 uu____2536 uu____2538))))));
(

let aux = (fun uu____2552 -> (

let uu____2553 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____2553) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____2574) -> begin
(

let uu____2575 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____2575) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____2588 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____2593 -> begin
(

let uu____2594 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____2594) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____2607 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let subst_c2 = (fun e1opt1 reason -> (match (((e1opt1), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____2665 = (

let uu____2670 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((uu____2670), (reason)))
in FStar_Util.Inl (uu____2665))
end
| uu____2677 -> begin
(aux ())
end))
in (

let try_simplify = (fun uu____2701 -> (

let maybe_close = (fun t x c -> (

let t1 = (FStar_TypeChecker_Normalize.normalize_refinement FStar_TypeChecker_Normalize.whnf_steps env t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____2719; FStar_Syntax_Syntax.index = uu____2720; FStar_Syntax_Syntax.sort = {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____2722; FStar_Syntax_Syntax.vars = uu____2723}}, uu____2724) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____2731 -> begin
c
end)))
in (

let uu____2732 = (

let uu____2733 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____2733))
in (match (uu____2732) with
| true -> begin
(

let uu____2744 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____2744) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____2757 -> begin
(

let uu____2758 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonTrivialPreConditionInPrims), ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")) uu____2758))
end))
end
| uu____2767 -> begin
(

let uu____2768 = ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2))
in (match (uu____2768) with
| true -> begin
(subst_c2 e1opt "both total")
end
| uu____2777 -> begin
(

let uu____2778 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____2778) with
| true -> begin
(

let uu____2787 = (

let uu____2792 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____2792), ("both gtot")))
in FStar_Util.Inl (uu____2787))
end
| uu____2797 -> begin
(match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____2816 = ((FStar_Syntax_Util.is_total_comp c1) && (

let uu____2818 = (FStar_Syntax_Syntax.is_null_bv x)
in (not (uu____2818))))
in (match (uu____2816) with
| true -> begin
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in (

let x1 = (

let uu___362_2831 = x
in {FStar_Syntax_Syntax.ppname = uu___362_2831.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___362_2831.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____2832 = (

let uu____2837 = (maybe_close x1.FStar_Syntax_Syntax.sort x1 c21)
in ((uu____2837), ("c1 Tot")))
in FStar_Util.Inl (uu____2832))))
end
| uu____2842 -> begin
(aux ())
end))
end
| uu____2843 -> begin
(aux ())
end)
end))
end))
end))))
in (

let uu____2852 = (try_simplify ())
in (match (uu____2852) with
| FStar_Util.Inl (c, reason) -> begin
((debug1 (fun uu____2872 -> (

let uu____2873 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "(2) bind: Simplified (because %s) to\n\t%s\n" reason uu____2873))));
c;
)
end
| FStar_Util.Inr (reason) -> begin
((debug1 (fun uu____2882 -> (FStar_Util.print1 "(2) bind: Not simplified because %s\n" reason)));
(

let mk_bind = (fun c11 b1 c21 -> (

let uu____2903 = (lift_and_destruct env c11 c21)
in (match (uu____2903) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b1) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2956 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____2956)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2976 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2976)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____3023 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____3032 = (

let uu____3043 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3052 = (

let uu____3063 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____3072 = (

let uu____3083 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____3092 = (

let uu____3103 = (

let uu____3112 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____3112))
in (uu____3103)::[])
in (uu____3083)::uu____3092))
in (uu____3063)::uu____3072))
in (uu____3043)::uu____3052))
in (uu____3023)::uu____3032))
in (

let wp = (

let uu____3164 = (

let uu____3169 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3169 wp_args))
in (uu____3164 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (mk_comp md u_t2 t2 wp bind_flags))))))
end)))
in (

let mk_seq = (fun c11 b1 c21 -> (

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in (

let uu____3194 = (FStar_TypeChecker_Env.join env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____3194) with
| (m, uu____3202, lift2) -> begin
(

let c23 = (

let uu____3205 = (lift_comp c22 m lift2)
in (FStar_Syntax_Syntax.mk_Comp uu____3205))
in (

let uu____3206 = (destruct_comp c12)
in (match (uu____3206) with
| (u1, t1, wp1) -> begin
(

let md_pure_or_ghost = (FStar_TypeChecker_Env.get_effect_decl env c12.FStar_Syntax_Syntax.effect_name)
in (

let vc1 = (

let uu____3220 = (

let uu____3225 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u1)::[]) env md_pure_or_ghost md_pure_or_ghost.FStar_Syntax_Syntax.trivial)
in (

let uu____3226 = (

let uu____3227 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3236 = (

let uu____3247 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____3247)::[])
in (uu____3227)::uu____3236))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3225 uu____3226)))
in (uu____3220 FStar_Pervasives_Native.None r1))
in (strengthen_comp env FStar_Pervasives_Native.None c23 vc1 bind_flags)))
end)))
end)))))
in (

let c1_typ = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____3286 = (destruct_comp c1_typ)
in (match (uu____3286) with
| (u_res_t1, res_t1, uu____3295) -> begin
(

let uu____3296 = ((FStar_Option.isSome b) && (should_return env e1opt lc11))
in (match (uu____3296) with
| true -> begin
(

let e1 = (FStar_Option.get e1opt)
in (

let x = (FStar_Option.get b)
in (

let uu____3299 = (FStar_Syntax_Util.is_partial_return c1)
in (match (uu____3299) with
| true -> begin
((debug1 (fun uu____3307 -> (

let uu____3308 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____3309 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case a): Substituting %s for %s" uu____3308 uu____3309)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (mk_bind c1 b c21));
)
end
| uu____3313 -> begin
(

let uu____3314 = (((FStar_Options.vcgen_optimize_bind_as_seq ()) && (lcomp_has_trivial_postcondition lc11)) && (

let uu____3316 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____3316)))
in (match (uu____3314) with
| true -> begin
(

let e1' = (

let uu____3336 = (FStar_Options.vcgen_decorate_with_type ())
in (match (uu____3336) with
| true -> begin
(FStar_Syntax_Util.mk_with_type u_res_t1 res_t1 e1)
end
| uu____3337 -> begin
e1
end))
in ((debug1 (fun uu____3345 -> (

let uu____3346 = (FStar_TypeChecker_Normalize.term_to_string env e1')
in (

let uu____3347 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case b): Substituting %s for %s" uu____3346 uu____3347)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1'))))::[]) c2)
in (mk_seq c1 b c21));
))
end
| uu____3351 -> begin
((debug1 (fun uu____3359 -> (

let uu____3360 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____3361 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case c): Adding equality %s = %s" uu____3360 uu____3361)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (

let x_eq_e = (

let uu____3366 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq2 u_res_t1 res_t1 e1 uu____3366))
in (

let c22 = (weaken_comp env c21 x_eq_e)
in (mk_bind c1 b c22))));
)
end))
end))))
end
| uu____3368 -> begin
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
| uu____3382 -> begin
g2
end))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let should_return1 = ((((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)) && (should_return env (FStar_Pervasives_Native.Some (e)) lc)) && (

let uu____3404 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____3404))))
in (

let flags1 = (match (should_return1) with
| true -> begin
(

let uu____3410 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____3410) with
| true -> begin
(FStar_Syntax_Syntax.RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____3413 -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end))
end
| uu____3414 -> begin
lc.FStar_Syntax_Syntax.cflags
end)
in (

let refine1 = (fun uu____3422 -> (

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

let uu____3426 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____3426) with
| true -> begin
(

let retc = (return_value env (FStar_Pervasives_Native.Some (u_t)) (FStar_Syntax_Util.comp_result c) e)
in (

let uu____3430 = (

let uu____3431 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____3431)))
in (match (uu____3430) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___363_3436 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___363_3436.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___363_3436.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___363_3436.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____3437 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags1)
end)))
end
| uu____3438 -> begin
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

let uu____3447 = (

let uu____3448 = (return_value env (FStar_Pervasives_Native.Some (u_t)) t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____3448 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3447))
in (

let eq1 = (FStar_Syntax_Util.mk_eq2 u_t t xexp e)
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____3451 = (

let uu____3452 = (

let uu____3453 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None uu____3453 ((FStar_Pervasives_Native.Some (x)), (eq_ret))))
in (FStar_Syntax_Syntax.lcomp_comp uu____3452))
in (FStar_Syntax_Util.comp_set_flags uu____3451 flags1))))))))))
end)))))
in (match ((not (should_return1))) with
| true -> begin
lc
end
| uu____3456 -> begin
(FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ flags1 refine1)
end)))))


let maybe_return_e2_and_bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r env e1opt lc1 e2 uu____3488 -> (match (uu____3488) with
| (x, lc2) -> begin
(

let lc21 = (

let eff1 = (FStar_TypeChecker_Env.norm_eff_name env lc1.FStar_Syntax_Syntax.eff_name)
in (

let eff2 = (FStar_TypeChecker_Env.norm_eff_name env lc2.FStar_Syntax_Syntax.eff_name)
in (

let uu____3500 = (((

let uu____3503 = (is_pure_or_ghost_effect env eff1)
in (not (uu____3503))) || (should_not_inline_lc lc1)) && (is_pure_or_ghost_effect env eff2))
in (match (uu____3500) with
| true -> begin
(maybe_assume_result_eq_pure_term env e2 lc2)
end
| uu____3504 -> begin
lc2
end))))
in (bind r env e1opt lc1 ((x), (lc21))))
end))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____3517 = (

let uu____3518 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____3518))
in (FStar_Syntax_Syntax.fvar uu____3517 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp)) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____3584 -> (match (uu____3584) with
| (uu____3597, eff_label, uu____3599, uu____3600) -> begin
(join_effects env eff eff_label)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let uu____3611 = (

let uu____3618 = (FStar_All.pipe_right lcases (FStar_Util.for_some (fun uu____3652 -> (match (uu____3652) with
| (uu____3665, uu____3666, flags1, uu____3668) -> begin
(FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___345_3682 -> (match (uu___345_3682) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____3683 -> begin
false
end))))
end))))
in (match (uu____3618) with
| true -> begin
((true), ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
end
| uu____3692 -> begin
((false), ([]))
end))
in (match (uu____3611) with
| (should_not_inline_whole_match, bind_cases_flags) -> begin
(

let bind_cases = (fun uu____3706 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____3708 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____3708) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____3709 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____3746 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____3747 = (

let uu____3752 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3753 = (

let uu____3754 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____3763 = (

let uu____3774 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____3783 = (

let uu____3794 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____3803 = (

let uu____3814 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____3814)::[])
in (uu____3794)::uu____3803))
in (uu____3774)::uu____3783))
in (uu____3754)::uu____3763))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3752 uu____3753)))
in (uu____3747 FStar_Pervasives_Native.None uu____3746))))
in (

let default_case = (

let post_k = (

let uu____3869 = (

let uu____3878 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____3878)::[])
in (

let uu____3897 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3869 uu____3897)))
in (

let kwp = (

let uu____3903 = (

let uu____3912 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____3912)::[])
in (

let uu____3931 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3903 uu____3931)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____3938 = (

let uu____3939 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____3939)::[])
in (

let uu____3958 = (

let uu____3961 = (

let uu____3968 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____3968))
in (

let uu____3969 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____3961 uu____3969)))
in (FStar_Syntax_Util.abs uu____3938 uu____3958 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let maybe_return = (fun eff_label_then cthen -> (

let uu____3991 = (should_not_inline_whole_match || (

let uu____3993 = (is_pure_or_ghost_effect env eff)
in (not (uu____3993))))
in (match (uu____3991) with
| true -> begin
(cthen true)
end
| uu____3994 -> begin
(cthen false)
end)))
in (

let comp = (FStar_List.fold_right (fun uu____4026 celse -> (match (uu____4026) with
| (g, eff_label, uu____4042, cthen) -> begin
(

let uu____4054 = (

let uu____4079 = (

let uu____4080 = (maybe_return eff_label cthen)
in (FStar_Syntax_Syntax.lcomp_comp uu____4080))
in (lift_and_destruct env uu____4079 celse))
in (match (uu____4054) with
| ((md, uu____4082, uu____4083), (uu____4084, uu____4085, wp_then), (uu____4087, uu____4088, wp_else)) -> begin
(

let uu____4108 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____4108 []))
end))
end)) lcases default_case)
in (match (lcases) with
| [] -> begin
comp
end
| (uu____4122)::[] -> begin
comp
end
| uu____4162 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____4180 = (destruct_comp comp1)
in (match (uu____4180) with
| (uu____4187, uu____4188, wp) -> begin
(

let wp1 = (

let uu____4193 = (

let uu____4198 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____4199 = (

let uu____4200 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4209 = (

let uu____4220 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4220)::[])
in (uu____4200)::uu____4209))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4198 uu____4199)))
in (uu____4193 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 bind_cases_flags))
end))))
end)))))
end))))
in (FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags bind_cases))
end))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____4287 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____4287) with
| FStar_Pervasives_Native.None -> begin
(match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(

let uu____4302 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq env e c c')
in (

let uu____4307 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____4302 uu____4307)))
end
| uu____4314 -> begin
(

let uu____4315 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____4320 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____4315 uu____4320)))
end)
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match (env.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
((e), (lc))
end
| uu____4356 -> begin
(

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____4364 = (

let uu____4365 = (FStar_Syntax_Subst.compress t2)
in uu____4365.FStar_Syntax_Syntax.n)
in (match (uu____4364) with
| FStar_Syntax_Syntax.Tm_type (uu____4368) -> begin
true
end
| uu____4369 -> begin
false
end))))
in (

let uu____4370 = (

let uu____4371 = (FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ)
in uu____4371.FStar_Syntax_Syntax.n)
in (match (uu____4370) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____4379 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (

let uu____4389 = (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____4389 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let lc1 = (

let uu____4391 = (

let uu____4392 = (

let uu____4393 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4393))
in ((FStar_Pervasives_Native.None), (uu____4392)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____4391))
in (

let e1 = (

let uu____4399 = (

let uu____4404 = (

let uu____4405 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4405)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4404))
in (uu____4399 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____4432 -> begin
((e), (lc))
end)))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> ((

let uu____4466 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____4466) with
| true -> begin
(

let uu____4467 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____4468 = (FStar_Syntax_Print.lcomp_to_string lc)
in (

let uu____4469 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n" uu____4467 uu____4468 uu____4469))))
end
| uu____4470 -> begin
()
end));
(

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____4475 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____4475) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____4498 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____4520 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4520), (false)))
end
| uu____4525 -> begin
(

let uu____4526 = (FStar_TypeChecker_Rel.get_subtyping_predicate env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____4526), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____4537) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____4546 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Errors.raise_error uu____4546 e.FStar_Syntax_Syntax.pos))
end
| uu____4557 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___364_4560 = lc
in {FStar_Syntax_Syntax.eff_name = uu___364_4560.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___364_4560.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___364_4560.FStar_Syntax_Syntax.comp_thunk})), (FStar_TypeChecker_Env.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____4565 = (FStar_TypeChecker_Env.guard_form g)
in (match (uu____4565) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let strengthen_trivial = (fun uu____4577 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let uu____4582 = ((

let uu____4585 = (

let uu____4586 = (FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name)
in (FStar_All.pipe_right uu____4586 (FStar_TypeChecker_Env.norm_eff_name env)))
in (FStar_All.pipe_right uu____4585 FStar_Syntax_Util.is_pure_or_ghost_effect)) || (

let uu____4590 = (FStar_Syntax_Util.eq_tm t res_t)
in (Prims.op_Equality uu____4590 FStar_Syntax_Util.Equal)))
in (match (uu____4582) with
| true -> begin
((

let uu____4592 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4592) with
| true -> begin
(

let uu____4593 = (FStar_Syntax_Print.lid_to_string (FStar_Syntax_Util.comp_effect_name c))
in (

let uu____4594 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____4595 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "weaken_result_type::strengthen_trivial: Not inserting the return since either the comp c:%s is pure/ghost or res_t:%s is same as t:%s\n" uu____4593 uu____4594 uu____4595))))
end
| uu____4596 -> begin
()
end));
(FStar_Syntax_Util.set_result_typ c t);
)
end
| uu____4597 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (res_t.FStar_Syntax_Syntax.pos)) res_t)
in (

let cret = (

let uu____4600 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env (comp_univ_opt c) res_t uu____4600))
in (

let lc1 = (

let uu____4602 = (FStar_Syntax_Util.lcomp_of_comp c)
in (

let uu____4603 = (

let uu____4604 = (FStar_Syntax_Util.lcomp_of_comp cret)
in ((FStar_Pervasives_Native.Some (x)), (uu____4604)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____4602 uu____4603)))
in ((

let uu____4608 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4608) with
| true -> begin
(

let uu____4609 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____4610 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____4611 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____4612 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (FStar_Util.print4 "weaken_result_type::strengthen_trivial: Inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n" uu____4609 uu____4610 uu____4611 uu____4612)))))
end
| uu____4613 -> begin
()
end));
(

let uu____4614 = (FStar_Syntax_Syntax.lcomp_comp lc1)
in (FStar_Syntax_Util.set_result_typ uu____4614 t));
))))
end)))))
in (

let lc1 = (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags strengthen_trivial)
in ((e), (lc1), (g))))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___365_4620 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___365_4620.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___365_4620.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___365_4620.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____4626 -> (

let uu____4627 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4627) with
| true -> begin
(FStar_Syntax_Syntax.lcomp_comp lc)
end
| uu____4628 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::[]) env f)
in (

let uu____4630 = (

let uu____4631 = (FStar_Syntax_Subst.compress f1)
in uu____4631.FStar_Syntax_Syntax.n)
in (match (uu____4630) with
| FStar_Syntax_Syntax.Tm_abs (uu____4634, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____4636; FStar_Syntax_Syntax.vars = uu____4637}, uu____4638) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___366_4664 = lc
in {FStar_Syntax_Syntax.eff_name = uu___366_4664.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___366_4664.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___366_4664.FStar_Syntax_Syntax.comp_thunk})
in (FStar_Syntax_Syntax.lcomp_comp lc1))
end
| uu____4665 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((

let uu____4668 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4668) with
| true -> begin
(

let uu____4669 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____4670 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____4671 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____4672 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____4669 uu____4670 uu____4671 uu____4672)))))
end
| uu____4673 -> begin
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

let uu____4681 = (

let uu____4686 = (

let uu____4687 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____4687)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____4686))
in (uu____4681 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____4714 -> begin
f1
end)
in (

let uu____4715 = (

let uu____4720 = (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____4737 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____4738 = (FStar_Syntax_Util.lcomp_of_comp cret)
in (

let uu____4739 = (FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____4720 uu____4737 e uu____4738 uu____4739)))))
in (match (uu____4715) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___367_4743 = x
in {FStar_Syntax_Syntax.ppname = uu___367_4743.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___367_4743.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____4745 = (FStar_Syntax_Util.lcomp_of_comp c)
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____4745 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((

let uu____4750 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4750) with
| true -> begin
(

let uu____4751 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____4751))
end
| uu____4752 -> begin
()
end));
c2;
))))
end)))))));
))
end)))
end)))
in (

let flags1 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___346_4761 -> (match (uu___346_4761) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____4764 -> begin
[]
end))))
in (

let lc1 = (

let uu____4766 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____4766 t flags1 strengthen))
in (

let g2 = (

let uu___368_4768 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___368_4768.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___368_4768.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___368_4768.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end)));
))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____4803 = (

let uu____4806 = (

let uu____4811 = (

let uu____4812 = (

let uu____4821 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____4821))
in (uu____4812)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____4811))
in (uu____4806 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____4803))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env t))
in (

let uu____4846 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____4846) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____4855 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____4862) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____4877) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____4893 = ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))
in (match (uu____4893) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____4907))::((ens, uu____4909))::uu____4910 -> begin
(

let uu____4953 = (

let uu____4956 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____4956))
in (

let uu____4957 = (

let uu____4958 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____4958))
in ((uu____4953), (uu____4957))))
end
| uu____4961 -> begin
(

let uu____4972 = (

let uu____4977 = (

let uu____4978 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____4978))
in ((FStar_Errors.Fatal_EffectConstructorNotFullyApplied), (uu____4977)))
in (FStar_Errors.raise_error uu____4972 comp.FStar_Syntax_Syntax.pos))
end)
end
| uu____4985 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____4994))::uu____4995 -> begin
(

let uu____5022 = (

let uu____5027 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5027))
in (match (uu____5022) with
| (us_r, uu____5059) -> begin
(

let uu____5060 = (

let uu____5065 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5065))
in (match (uu____5060) with
| (us_e, uu____5097) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____5100 = (

let uu____5101 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar uu____5101 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5100 us_r))
in (

let as_ens = (

let uu____5103 = (

let uu____5104 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar uu____5104 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5103 us_e))
in (

let req = (

let uu____5108 = (

let uu____5113 = (

let uu____5114 = (

let uu____5125 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5125)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____5114)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____5113))
in (uu____5108 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____5167 = (

let uu____5172 = (

let uu____5173 = (

let uu____5184 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5184)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____5173)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____5172))
in (uu____5167 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____5223 = (

let uu____5226 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____5226))
in (

let uu____5227 = (

let uu____5228 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____5228))
in ((uu____5223), (uu____5227)))))))))
end))
end))
end
| uu____5231 -> begin
(failwith "Impossible")
end))
end))
end)
end)))))


let reify_body : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let tm = (FStar_Syntax_Util.mk_reify t)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____5263 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____5263) with
| true -> begin
(

let uu____5264 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____5265 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____5264 uu____5265)))
end
| uu____5266 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____5315 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____5315) with
| true -> begin
(

let uu____5316 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____5317 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____5316 uu____5317)))
end
| uu____5318 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____5324 = (

let uu____5325 = (

let uu____5326 = (FStar_Syntax_Subst.compress t)
in uu____5326.FStar_Syntax_Syntax.n)
in (match (uu____5325) with
| FStar_Syntax_Syntax.Tm_app (uu____5329) -> begin
false
end
| uu____5346 -> begin
true
end))
in (match (uu____5324) with
| true -> begin
t
end
| uu____5347 -> begin
(

let uu____5348 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____5348) with
| (head1, args) -> begin
(

let uu____5391 = (

let uu____5392 = (

let uu____5393 = (FStar_Syntax_Subst.compress head1)
in uu____5393.FStar_Syntax_Syntax.n)
in (match (uu____5392) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____5396 -> begin
false
end))
in (match (uu____5391) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____5426 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____5437 -> begin
t
end))
end))
end)))


let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let torig = (FStar_Syntax_Subst.compress t)
in (match ((not (env.FStar_TypeChecker_Env.instantiate_imp))) with
| true -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____5466 -> begin
((

let uu____5468 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5468) with
| true -> begin
(

let uu____5469 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5470 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____5471 = (

let uu____5472 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Common.string_of_option FStar_Syntax_Print.term_to_string uu____5472))
in (FStar_Util.print3 "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n" uu____5469 uu____5470 uu____5471))))
end
| uu____5475 -> begin
()
end));
(

let number_of_implicits = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____5483 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____5483) with
| (formals, uu____5499) -> begin
(

let n_implicits = (

let uu____5521 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____5599 -> (match (uu____5599) with
| (uu____5606, imp) -> begin
((FStar_Option.isNone imp) || (

let uu____5613 = (FStar_Syntax_Util.eq_aqual imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)))
in (Prims.op_Equality uu____5613 FStar_Syntax_Util.Equal)))
end))))
in (match (uu____5521) with
| FStar_Pervasives_Native.None -> begin
(FStar_List.length formals)
end
| FStar_Pervasives_Native.Some (implicits, _first_explicit, _rest) -> begin
(FStar_List.length implicits)
end))
in n_implicits)
end))))
in (

let inst_n_binders = (fun t1 -> (

let uu____5739 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____5739) with
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

let uu____5763 = (

let uu____5768 = (

let uu____5769 = (FStar_Util.string_of_int n_expected)
in (

let uu____5776 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5777 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____5769 uu____5776 uu____5777))))
in ((FStar_Errors.Fatal_MissingImplicitArguments), (uu____5768)))
in (

let uu____5784 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____5763 uu____5784)))
end
| uu____5787 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___347_5807 -> (match (uu___347_5807) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (i) -> begin
FStar_Pervasives_Native.Some ((i - (Prims.parse_int "1")))
end))
in (

let t1 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____5842 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____5842) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_2), uu____5957) when (_0_2 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Env.trivial_guard))
end
| (uu____6000, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6002))))::rest) -> begin
(

let t2 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____6033 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t2)
in (match (uu____6033) with
| (v1, uu____6073, g) -> begin
((

let uu____6088 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6088) with
| true -> begin
(

let uu____6089 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.print1 "maybe_instantiate: Instantiating implicit with %s\n" uu____6089))
end
| uu____6090 -> begin
()
end));
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____6096 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____6096) with
| (args, bs3, subst3, g') -> begin
(

let uu____6189 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::args), (bs3), (subst3), (uu____6189)))
end)));
)
end)))
end
| (uu____6216, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau))))::rest) -> begin
(

let t2 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____6251 = (new_implicit_var "Instantiation of meta argument" e.FStar_Syntax_Syntax.pos env t2)
in (match (uu____6251) with
| (v1, uu____6291, g) -> begin
((

let uu____6306 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6306) with
| true -> begin
(

let uu____6307 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.print1 "maybe_instantiate: Instantiating meta argument with %s\n" uu____6307))
end
| uu____6308 -> begin
()
end));
(

let mark_meta_implicits = (fun tau1 g1 -> (

let uu___369_6320 = g1
in (

let uu____6321 = (FStar_List.map (fun imp -> (

let uu___370_6327 = imp
in {FStar_TypeChecker_Env.imp_reason = uu___370_6327.FStar_TypeChecker_Env.imp_reason; FStar_TypeChecker_Env.imp_uvar = uu___370_6327.FStar_TypeChecker_Env.imp_uvar; FStar_TypeChecker_Env.imp_tm = uu___370_6327.FStar_TypeChecker_Env.imp_tm; FStar_TypeChecker_Env.imp_range = uu___370_6327.FStar_TypeChecker_Env.imp_range; FStar_TypeChecker_Env.imp_meta = FStar_Pervasives_Native.Some (((env), (tau1)))})) g1.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___369_6320.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___369_6320.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___369_6320.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____6321})))
in (

let g1 = (mark_meta_implicits tau g)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____6338 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____6338) with
| (args, bs3, subst3, g') -> begin
(

let uu____6431 = (FStar_TypeChecker_Env.conj_guard g1 g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::args), (bs3), (subst3), (uu____6431)))
end)))));
)
end)))
end
| (uu____6458, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Env.trivial_guard))
end))
in (

let uu____6504 = (

let uu____6531 = (inst_n_binders t1)
in (aux [] uu____6531 bs1))
in (match (uu____6504) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____6602) -> begin
((e), (torig), (guard))
end
| (uu____6633, []) when (

let uu____6664 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____6664))) -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____6665 -> begin
(

let t2 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____6693 -> begin
(FStar_Syntax_Util.arrow bs2 c1)
end)
in (

let t3 = (FStar_Syntax_Subst.subst subst1 t2)
in (

let e1 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in ((e1), (t3), (guard)))))
end)
end)))
end))
end
| uu____6706 -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end)))));
)
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____6716 = (

let uu____6719 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____6719 (FStar_List.map (fun u -> (

let uu____6729 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____6729 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____6716 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____6750 = (FStar_Util.set_is_empty x)
in (match (uu____6750) with
| true -> begin
[]
end
| uu____6753 -> begin
(

let s = (

let uu____6765 = (

let uu____6768 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____6768))
in (FStar_All.pipe_right uu____6765 FStar_Util.set_elements))
in ((

let uu____6784 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____6784) with
| true -> begin
(

let uu____6785 = (

let uu____6786 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____6786))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____6785))
end
| uu____6789 -> begin
()
end));
(

let r = (

let uu____6793 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____6793))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____6832 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____6832) with
| true -> begin
(

let uu____6833 = (

let uu____6834 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____6834))
in (

let uu____6835 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____6836 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____6833 uu____6835 uu____6836))))
end
| uu____6837 -> begin
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

let uu____6862 = (FStar_Util.set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____6862 FStar_Util.set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____6900) -> begin
generalized_univ_names
end
| (uu____6907, []) -> begin
explicit_univ_names
end
| uu____6914 -> begin
(

let uu____6923 = (

let uu____6928 = (

let uu____6929 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____6929))
in ((FStar_Errors.Fatal_UnexpectedGeneralizedUniverse), (uu____6928)))
in (FStar_Errors.raise_error uu____6923 t.FStar_Syntax_Syntax.pos))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in ((

let uu____6947 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____6947) with
| true -> begin
(

let uu____6948 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____6949 = (FStar_Syntax_Print.univ_names_to_string univnames1)
in (FStar_Util.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" uu____6948 uu____6949)))
end
| uu____6950 -> begin
()
end));
(

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____6955 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____6955) with
| true -> begin
(

let uu____6956 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____6956))
end
| uu____6957 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____6962 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____6962) with
| true -> begin
(

let uu____6963 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____6964 = (FStar_Syntax_Print.univ_names_to_string gen1)
in (FStar_Util.print2 "After generalization, t: %s and univs: %s\n" uu____6963 uu____6964)))
end
| uu____6965 -> begin
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

let uu____7042 = (

let uu____7043 = (FStar_Util.for_all (fun uu____7056 -> (match (uu____7056) with
| (uu____7065, uu____7066, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____7043))
in (match (uu____7042) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7106 -> begin
(

let norm1 = (fun c -> ((

let uu____7114 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____7114) with
| true -> begin
(

let uu____7115 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____7115))
end
| uu____7116 -> begin
()
end));
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env c)
in ((

let uu____7119 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____7119) with
| true -> begin
(

let uu____7120 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7120))
end
| uu____7121 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____7135 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____7135 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____7169 -> (match (uu____7169) with
| (lbname, e, c) -> begin
(

let c1 = (norm1 c)
in (

let t = (FStar_Syntax_Util.comp_result c1)
in (

let univs1 = (FStar_Syntax_Free.univs t)
in (

let uvt = (FStar_Syntax_Free.uvars t)
in ((

let uu____7206 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7206) with
| true -> begin
(

let uu____7207 = (

let uu____7208 = (

let uu____7211 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____7211 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____7208 (FStar_String.concat ", ")))
in (

let uu____7254 = (

let uu____7255 = (

let uu____7258 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____7258 (FStar_List.map (fun u -> (

let uu____7269 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____7270 = (FStar_Syntax_Print.term_to_string u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____7269 uu____7270)))))))
in (FStar_All.pipe_right uu____7255 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____7207 uu____7254)))
end
| uu____7273 -> begin
()
end));
(

let univs2 = (

let uu____7277 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uv -> (

let uu____7289 = (FStar_Syntax_Free.univs uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.set_union univs2 uu____7289))) univs1 uu____7277))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____7296 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7296) with
| true -> begin
(

let uu____7297 = (

let uu____7298 = (

let uu____7301 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____7301 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____7298 (FStar_String.concat ", ")))
in (

let uu____7344 = (

let uu____7345 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> (

let uu____7356 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____7357 = (FStar_TypeChecker_Normalize.term_to_string env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____7356 uu____7357))))))
in (FStar_All.pipe_right uu____7345 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____7297 uu____7344)))
end
| uu____7360 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
)))))
end))
in (

let uu____7371 = (

let uu____7388 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____7388))
in (match (uu____7371) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____7478 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____7478) with
| true -> begin
()
end
| uu____7479 -> begin
(

let uu____7480 = lec_hd
in (match (uu____7480) with
| (lb1, uu____7488, uu____7489) -> begin
(

let uu____7490 = lec2
in (match (uu____7490) with
| (lb2, uu____7498, uu____7499) -> begin
(

let msg = (

let uu____7501 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____7502 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____7501 uu____7502)))
in (

let uu____7503 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleSetOfUniverse), (msg)) uu____7503)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun u -> (FStar_All.pipe_right u21 (FStar_Util.for_some (fun u' -> (FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head u'.FStar_Syntax_Syntax.ctx_uvar_head))))))))
in (

let uu____7567 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____7567) with
| true -> begin
()
end
| uu____7568 -> begin
(

let uu____7569 = lec_hd
in (match (uu____7569) with
| (lb1, uu____7577, uu____7578) -> begin
(

let uu____7579 = lec2
in (match (uu____7579) with
| (lb2, uu____7587, uu____7588) -> begin
(

let msg = (

let uu____7590 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____7591 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____7590 uu____7591)))
in (

let uu____7592 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleNumberOfTypes), (msg)) uu____7592)))
end))
end))
end))))
in (

let lecs1 = (

let uu____7602 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____7655 = (univs_and_uvars_of_lec this_lec)
in (match (uu____7655) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____7602 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail1 = (fun k -> (

let uu____7756 = lec_hd
in (match (uu____7756) with
| (lbname, e, c) -> begin
(

let uu____7766 = (

let uu____7771 = (

let uu____7772 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____7773 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____7774 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____7772 uu____7773 uu____7774))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____7771)))
in (

let uu____7775 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____7766 uu____7775)))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun u -> (

let uu____7796 = (FStar_Syntax_Unionfind.find u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____7796) with
| FStar_Pervasives_Native.Some (uu____7805) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____7812 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____7816 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____7816) with
| (bs, kres) -> begin
((

let uu____7860 = (

let uu____7861 = (

let uu____7864 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____7864))
in uu____7861.FStar_Syntax_Syntax.n)
in (match (uu____7860) with
| FStar_Syntax_Syntax.Tm_type (uu____7865) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____7869 = (

let uu____7870 = (FStar_Util.set_is_empty free)
in (not (uu____7870)))
in (match (uu____7869) with
| true -> begin
(fail1 kres)
end
| uu____7871 -> begin
()
end)))
end
| uu____7872 -> begin
(fail1 kres)
end));
(

let a = (

let uu____7874 = (

let uu____7877 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_3 -> FStar_Pervasives_Native.Some (_0_3)) uu____7877))
in (FStar_Syntax_Syntax.new_bv uu____7874 kres))
in (

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Syntax.bv_to_name a)
end
| uu____7887 -> begin
(

let uu____7896 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____7896 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
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

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____8003 -> (match (uu____8003) with
| (lbname, e, c) -> begin
(

let uu____8051 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____8126 -> begin
(

let uu____8141 = ((e), (c))
in (match (uu____8141) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____8184 -> (match (uu____8184) with
| (x, uu____8192) -> begin
(

let uu____8197 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____8197))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____8215 = (

let uu____8216 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____8216))
in (match (uu____8215) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____8219 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____8220 -> begin
e1
end)
in (

let t = (

let uu____8222 = (

let uu____8223 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____8223.FStar_Syntax_Syntax.n)
in (match (uu____8222) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____8248 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____8248) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____8261 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____8265 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____8265), (gen_tvars))))))))
end))
end)
in (match (uu____8051) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____8419 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____8419) with
| true -> begin
(

let uu____8420 = (

let uu____8421 = (FStar_List.map (fun uu____8434 -> (match (uu____8434) with
| (lb, uu____8442, uu____8443) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____8421 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____8420))
end
| uu____8446 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____8464 -> (match (uu____8464) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____8493 = (gen env is_rec lecs)
in (match (uu____8493) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____8592 -> (match (uu____8592) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____8654 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8654) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____8700 -> (match (uu____8700) with
| (l, us, e, c, gvs) -> begin
(

let uu____8734 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____8735 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____8736 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____8737 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____8738 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____8734 uu____8735 uu____8736 uu____8737 uu____8738))))))
end))))
end
| uu____8739 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____8779 -> (match (uu____8779) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____8823 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____8823), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check1 = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____8879 -> begin
(

let uu____8880 = (FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21)
in (match (uu____8880) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____8886 = (FStar_TypeChecker_Env.apply_guard f e)
in (FStar_All.pipe_left (fun _0_4 -> FStar_Pervasives_Native.Some (_0_4)) uu____8886))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____8895 = (

let uu____8896 = (FStar_Syntax_Subst.compress e1)
in uu____8896.FStar_Syntax_Syntax.n)
in (match (uu____8895) with
| FStar_Syntax_Syntax.Tm_name (uu____8899) -> begin
true
end
| uu____8900 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___371_8920 = x
in {FStar_Syntax_Syntax.ppname = uu___371_8920.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___371_8920.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____8921 -> begin
e2
end)))
in (

let env2 = (

let uu___372_8923 = env1
in (

let uu____8924 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___372_8923.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___372_8923.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___372_8923.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___372_8923.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___372_8923.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___372_8923.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___372_8923.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___372_8923.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___372_8923.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___372_8923.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___372_8923.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___372_8923.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___372_8923.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___372_8923.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___372_8923.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___372_8923.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___372_8923.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____8924; FStar_TypeChecker_Env.is_iface = uu___372_8923.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___372_8923.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___372_8923.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___372_8923.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___372_8923.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___372_8923.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___372_8923.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___372_8923.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___372_8923.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___372_8923.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___372_8923.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___372_8923.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___372_8923.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___372_8923.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___372_8923.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___372_8923.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___372_8923.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___372_8923.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___372_8923.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___372_8923.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___372_8923.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___372_8923.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___372_8923.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___372_8923.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___372_8923.FStar_TypeChecker_Env.nbe}))
in (

let uu____8925 = (check1 env2 t1 t2)
in (match (uu____8925) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8932 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____8937 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____8932 uu____8937)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____8944 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____8944) with
| true -> begin
(

let uu____8945 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____8945))
end
| uu____8946 -> begin
()
end));
(

let uu____8947 = (decorate e t2)
in ((uu____8947), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> ((

let uu____8972 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____8972) with
| true -> begin
(

let uu____8973 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "check_top_level, lc = %s\n" uu____8973))
end
| uu____8974 -> begin
()
end));
(

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____8983 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____8983) with
| true -> begin
(

let uu____8988 = (discharge g1)
in (

let uu____8989 = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((uu____8988), (uu____8989))))
end
| uu____8990 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let steps = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]
in (

let c1 = (

let uu____8996 = (

let uu____8997 = (

let uu____8998 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____8998 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____8997 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____8996 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____9000 = (destruct_comp c1)
in (match (uu____9000) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____9017 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____9018 = (

let uu____9023 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____9024 = (

let uu____9025 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____9034 = (

let uu____9045 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____9045)::[])
in (uu____9025)::uu____9034))
in (FStar_Syntax_Syntax.mk_Tm_app uu____9023 uu____9024)))
in (uu____9018 FStar_Pervasives_Native.None uu____9017)))
in ((

let uu____9081 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____9081) with
| true -> begin
(

let uu____9082 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____9082))
end
| uu____9083 -> begin
()
end));
(

let g2 = (

let uu____9085 = (FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Env.conj_guard g1 uu____9085))
in (

let uu____9086 = (discharge g2)
in (

let uu____9087 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____9086), (uu____9087)))));
))
end))))))
end))));
))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___348_9119 -> (match (uu___348_9119) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____9129))::[] -> begin
(f fst1)
end
| uu____9154 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____9165 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____9165 (fun _0_5 -> FStar_TypeChecker_Common.NonTrivial (_0_5)))))
in (

let op_or_e = (fun e -> (

let uu____9176 = (

let uu____9177 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____9177))
in (FStar_All.pipe_right uu____9176 (fun _0_6 -> FStar_TypeChecker_Common.NonTrivial (_0_6)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_7 -> FStar_TypeChecker_Common.NonTrivial (_0_7))))
in (

let op_or_t = (fun t -> (

let uu____9196 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____9196 (fun _0_8 -> FStar_TypeChecker_Common.NonTrivial (_0_8)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_9 -> FStar_TypeChecker_Common.NonTrivial (_0_9))))
in (

let short_op_ite = (fun uu___349_9210 -> (match (uu___349_9210) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____9220))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____9247))::[] -> begin
(

let uu____9288 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____9288 (fun _0_10 -> FStar_TypeChecker_Common.NonTrivial (_0_10))))
end
| uu____9289 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____9300 = (

let uu____9308 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____9308)))
in (

let uu____9316 = (

let uu____9326 = (

let uu____9334 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____9334)))
in (

let uu____9342 = (

let uu____9352 = (

let uu____9360 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____9360)))
in (

let uu____9368 = (

let uu____9378 = (

let uu____9386 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____9386)))
in (

let uu____9394 = (

let uu____9404 = (

let uu____9412 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____9412)))
in (uu____9404)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____9378)::uu____9394))
in (uu____9352)::uu____9368))
in (uu____9326)::uu____9342))
in (uu____9300)::uu____9316))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9474 = (FStar_Util.find_map table (fun uu____9489 -> (match (uu____9489) with
| (x, mk1) -> begin
(

let uu____9506 = (FStar_Ident.lid_equals x lid)
in (match (uu____9506) with
| true -> begin
(

let uu____9509 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____9509))
end
| uu____9510 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (uu____9474) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____9512 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____9518 = (

let uu____9519 = (FStar_Syntax_Util.un_uinst l)
in uu____9519.FStar_Syntax_Syntax.n)
in (match (uu____9518) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____9523 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____9557))::uu____9558 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____9577 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____9586, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9587))))::uu____9588 -> begin
bs
end
| uu____9605 -> begin
(

let uu____9606 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____9606) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____9610 = (

let uu____9611 = (FStar_Syntax_Subst.compress t)
in uu____9611.FStar_Syntax_Syntax.n)
in (match (uu____9610) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____9615) -> begin
(

let uu____9636 = (FStar_Util.prefix_until (fun uu___350_9676 -> (match (uu___350_9676) with
| (uu____9683, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9684))) -> begin
false
end
| uu____9687 -> begin
true
end)) bs')
in (match (uu____9636) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____9722, uu____9723) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____9795, uu____9796) -> begin
(

let uu____9869 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____9887 -> (match (uu____9887) with
| (x, uu____9895) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____9869) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____9942 -> (match (uu____9942) with
| (x, i) -> begin
(

let uu____9961 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____9961), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____9970 -> begin
bs
end))
end))
end
| uu____9971 -> begin
bs
end))
end))
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 t -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in (

let uu____9999 = (((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1)))
in (match (uu____9999) with
| true -> begin
e
end
| uu____10000 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end)))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____10026 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____10026) with
| true -> begin
e
end
| uu____10027 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____10061 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____10061) with
| true -> begin
((

let uu____10063 = (FStar_Ident.text_of_lid lident)
in (d uu____10063));
(

let uu____10064 = (FStar_Ident.text_of_lid lident)
in (

let uu____10065 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" uu____10064 uu____10065)));
)
end
| uu____10066 -> begin
()
end));
(

let fv = (

let uu____10068 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____10068 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (((FStar_Syntax_Util.mk_letbinding lbname [] FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def [] FStar_Range.dummyRange))::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____10078 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___373_10080 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___373_10080.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___373_10080.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___373_10080.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___373_10080.FStar_Syntax_Syntax.sigattrs})), (uu____10078)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (

let visibility = (fun uu___351_10096 -> (match (uu___351_10096) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____10097 -> begin
false
end))
in (

let reducibility = (fun uu___352_10103 -> (match (uu___352_10103) with
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
| uu____10104 -> begin
false
end))
in (

let assumption = (fun uu___353_10110 -> (match (uu___353_10110) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____10111 -> begin
false
end))
in (

let reification = (fun uu___354_10117 -> (match (uu___354_10117) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____10118) -> begin
true
end
| uu____10119 -> begin
false
end))
in (

let inferred = (fun uu___355_10125 -> (match (uu___355_10125) with
| FStar_Syntax_Syntax.Discriminator (uu____10126) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____10127) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____10132) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____10141) -> begin
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
| uu____10150 -> begin
false
end))
in (

let has_eq = (fun uu___356_10156 -> (match (uu___356_10156) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____10157 -> begin
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
| FStar_Syntax_Syntax.Reflectable (uu____10221) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____10226 -> begin
true
end))
in (

let quals = (FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se) (FStar_List.filter (fun x -> (not ((Prims.op_Equality x FStar_Syntax_Syntax.Logic))))))
in (

let uu____10236 = (

let uu____10237 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___357_10241 -> (match (uu___357_10241) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____10242 -> begin
false
end))))
in (FStar_All.pipe_right uu____10237 Prims.op_Negation))
in (match (uu____10236) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____10257 = (

let uu____10262 = (

let uu____10263 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____10263 msg))
in ((FStar_Errors.Fatal_QulifierListNotPermitted), (uu____10262)))
in (FStar_Errors.raise_error uu____10257 r)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____10275 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____10277 -> begin
()
end);
(

let uu____10279 = (

let uu____10280 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____10280)))
in (match (uu____10279) with
| true -> begin
(err "ill-formed combination")
end
| uu____10283 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____10285), uu____10286) -> begin
((

let uu____10296 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____10296) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____10299 -> begin
()
end));
(

let uu____10300 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____10300) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____10305 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____10306) -> begin
(

let uu____10315 = (

let uu____10316 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____10316)))
in (match (uu____10315) with
| true -> begin
(err'1 ())
end
| uu____10321 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____10322) -> begin
(

let uu____10329 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____10329) with
| true -> begin
(err'1 ())
end
| uu____10332 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____10333) -> begin
(

let uu____10340 = (

let uu____10341 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____10341)))
in (match (uu____10340) with
| true -> begin
(err'1 ())
end
| uu____10346 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____10347) -> begin
(

let uu____10348 = (

let uu____10349 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____10349)))
in (match (uu____10348) with
| true -> begin
(err'1 ())
end
| uu____10354 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____10355) -> begin
(

let uu____10356 = (

let uu____10357 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____10357)))
in (match (uu____10356) with
| true -> begin
(err'1 ())
end
| uu____10362 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____10363) -> begin
(

let uu____10376 = (

let uu____10377 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____10377)))
in (match (uu____10376) with
| true -> begin
(err'1 ())
end
| uu____10382 -> begin
()
end))
end
| uu____10383 -> begin
()
end);
))))))
end
| uu____10384 -> begin
()
end)))))))))))


let must_erase_for_extraction : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun g t -> (

let has_erased_for_extraction_attr = (fun fv -> (

let uu____10401 = (

let uu____10406 = (FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv)
in (FStar_All.pipe_right uu____10406 (FStar_TypeChecker_Env.lookup_attrs_of_lid g)))
in (FStar_All.pipe_right uu____10401 (fun l_opt -> ((FStar_Util.is_some l_opt) && (

let uu____10424 = (FStar_All.pipe_right l_opt FStar_Util.must)
in (FStar_All.pipe_right uu____10424 (FStar_List.existsb (fun t1 -> (

let uu____10441 = (

let uu____10442 = (FStar_Syntax_Subst.compress t1)
in uu____10442.FStar_Syntax_Syntax.n)
in (match (uu____10441) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_Ident.lid_equals fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.must_erase_for_extraction_attr) -> begin
true
end
| uu____10446 -> begin
false
end)))))))))))
in (

let rec aux_whnf = (fun env t1 -> (

let uu____10469 = (

let uu____10470 = (FStar_Syntax_Subst.compress t1)
in uu____10470.FStar_Syntax_Syntax.n)
in (match (uu____10469) with
| FStar_Syntax_Syntax.Tm_type (uu____10473) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (has_erased_for_extraction_attr fv))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____10475) -> begin
(

let uu____10490 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____10490) with
| (bs, c) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____10522 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____10522) with
| true -> begin
(aux env1 (FStar_Syntax_Util.comp_result c))
end
| uu____10523 -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____10524; FStar_Syntax_Syntax.index = uu____10525; FStar_Syntax_Syntax.sort = t2}, uu____10527) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____10535, uu____10536) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____10578)::[]) -> begin
(

let uu____10617 = (

let uu____10618 = (FStar_Syntax_Util.un_uinst head1)
in uu____10618.FStar_Syntax_Syntax.n)
in (match (uu____10617) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid) || (has_erased_for_extraction_attr fv))
end
| uu____10622 -> begin
false
end))
end
| uu____10623 -> begin
false
end)))
and aux = (fun env t1 -> (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::[]) env t1)
in (

let res = (aux_whnf env t2)
in ((

let uu____10631 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Extraction")))
in (match (uu____10631) with
| true -> begin
(

let uu____10632 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "must_erase=%s: %s\n" (match (res) with
| true -> begin
"true"
end
| uu____10633 -> begin
"false"
end) uu____10632))
end
| uu____10634 -> begin
()
end));
res;
))))
in (aux g t))))




