
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  unit = (fun env errs -> (

let uu____23 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____24 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.log_issue uu____23 uu____24))))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (FStar_TypeChecker_Env.new_implicit_var_aux reason r env k FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None))


let close_guard_implicits : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env xs g -> (

let uu____85 = (

let uu____87 = (FStar_Options.eager_subtyping ())
in (FStar_All.pipe_left Prims.op_Negation uu____87))
in (match (uu____85) with
| true -> begin
g
end
| uu____92 -> begin
(

let uu____94 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred (FStar_List.partition (fun uu____146 -> (match (uu____146) with
| (uu____153, p) -> begin
(FStar_TypeChecker_Rel.flex_prob_closing env xs p)
end))))
in (match (uu____94) with
| (solve_now, defer) -> begin
((

let uu____188 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____188) with
| true -> begin
((FStar_Util.print_string "SOLVE BEFORE CLOSING:\n");
(FStar_List.iter (fun uu____205 -> (match (uu____205) with
| (s, p) -> begin
(

let uu____215 = (FStar_TypeChecker_Rel.prob_to_string env p)
in (FStar_Util.print2 "%s: %s\n" s uu____215))
end)) solve_now);
(FStar_Util.print_string " ...DEFERRED THE REST:\n");
(FStar_List.iter (fun uu____230 -> (match (uu____230) with
| (s, p) -> begin
(

let uu____240 = (FStar_TypeChecker_Rel.prob_to_string env p)
in (FStar_Util.print2 "%s: %s\n" s uu____240))
end)) defer);
(FStar_Util.print_string "END\n");
)
end
| uu____244 -> begin
()
end));
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env (

let uu___361_248 = g
in {FStar_TypeChecker_Env.guard_f = uu___361_248.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = solve_now; FStar_TypeChecker_Env.univ_ineqs = uu___361_248.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___361_248.FStar_TypeChecker_Env.implicits}))
in (

let g2 = (

let uu___362_250 = g1
in {FStar_TypeChecker_Env.guard_f = uu___362_250.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = defer; FStar_TypeChecker_Env.univ_ineqs = uu___362_250.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___362_250.FStar_TypeChecker_Env.implicits})
in g2));
)
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____265 = (

let uu____267 = (FStar_Util.set_is_empty uvs)
in (not (uu____267)))
in (match (uu____265) with
| true -> begin
(

let us = (

let uu____272 = (

let uu____276 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun u -> (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)) uu____276))
in (FStar_All.pipe_right uu____272 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____295 = (

let uu____301 = (

let uu____303 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____303))
in ((FStar_Errors.Error_UncontrainedUnificationVar), (uu____301)))
in (FStar_Errors.log_issue r uu____295));
(FStar_Options.pop ());
))
end
| uu____307 -> begin
()
end))))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____326 -> (match (uu____326) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____337; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____339; FStar_Syntax_Syntax.lbpos = uu____340} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____375 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 e)
in (match (uu____375) with
| (univ_vars2, e1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars2)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let rec aux = (fun e2 -> (

let e3 = (FStar_Syntax_Subst.compress e2)
in (match (e3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e4, uu____413) -> begin
(aux e4)
end
| FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____420) -> begin
(FStar_Pervasives_Native.fst t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____475) -> begin
(

let res = (aux body)
in (

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____511 = (FStar_Options.ml_ish ())
in (match (uu____511) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____516 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in ((

let uu____533 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____533) with
| true -> begin
(

let uu____536 = (FStar_Range.string_of_range r)
in (

let uu____538 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Using type %s\n" uu____536 uu____538)))
end
| uu____541 -> begin
()
end));
FStar_Util.Inl (t2);
))))
end
| uu____543 -> begin
FStar_Util.Inl (FStar_Syntax_Syntax.tun)
end)))
in (

let t2 = (

let uu____545 = (aux e1)
in (match (uu____545) with
| FStar_Util.Inr (c) -> begin
(

let uu____551 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____551) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____554 -> begin
(

let uu____556 = (

let uu____562 = (

let uu____564 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____564))
in ((FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec), (uu____562)))
in (FStar_Errors.raise_error uu____556 rng))
end))
end
| FStar_Util.Inl (t2) -> begin
t2
end))
in ((univ_vars2), (t2), (true))))))
end))
end
| uu____573 -> begin
(

let uu____574 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____574) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____638 -> (match (uu____638) with
| (p, i) -> begin
(

let uu____658 = (decorated_pattern_as_term p)
in (match (uu____658) with
| (vars, te) -> begin
(

let uu____681 = (

let uu____686 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____686)))
in ((vars), (uu____681)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____700 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____700)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____704 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____704)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____708 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____708)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____731 = (

let uu____750 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____750 FStar_List.unzip))
in (match (uu____731) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____888 = (

let uu____889 = (

let uu____890 = (

let uu____907 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____907), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____890))
in (mk1 uu____889))
in ((vars1), (uu____888))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let comp_univ_opt : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____946, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.GTotal (uu____956, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::uu____970 -> begin
FStar_Pervasives_Native.Some (hd1)
end)
end))


let lcomp_univ_opt : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun lc -> (

let uu____981 = (FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp)
in (FStar_All.pipe_right uu____981 comp_univ_opt)))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____1010))::[] -> begin
wp
end
| uu____1035 -> begin
(

let uu____1046 = (

let uu____1048 = (

let uu____1050 = (FStar_List.map (fun uu____1064 -> (match (uu____1064) with
| (x, uu____1073) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____1050 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____1048))
in (failwith uu____1046))
end)
in (

let uu____1084 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____1084), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____1101 = (destruct_comp c)
in (match (uu____1101) with
| (u, uu____1109, wp) -> begin
(

let uu____1111 = (

let uu____1122 = (

let uu____1131 = (lift.FStar_TypeChecker_Env.mlift_wp u c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____1131))
in (uu____1122)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____1111; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____1164 = (

let uu____1171 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____1172 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____1171 uu____1172)))
in (match (uu____1164) with
| (m, uu____1174, uu____1175) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____1192 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____1192) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____1195 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____1239 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____1239) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____1276 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____1276) with
| (a, kwp) -> begin
(

let uu____1307 = (destruct_comp m1)
in (

let uu____1314 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____1307), (uu____1314))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags1 -> (

let uu____1399 = (

let uu____1400 = (

let uu____1411 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1411)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____1400; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp uu____1399)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags1 -> (

let uu____1495 = (FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)
in (match (uu____1495) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____1498 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1)
end)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu____1511 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____1511 lc.FStar_Syntax_Syntax.cflags (fun uu____1514 -> (

let uu____1515 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Subst.subst_comp subst1 uu____1515))))))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1523 = (

let uu____1524 = (FStar_Syntax_Subst.compress t)
in uu____1524.FStar_Syntax_Syntax.n)
in (match (uu____1523) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1528) -> begin
true
end
| uu____1544 -> begin
false
end)))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (reason1) -> begin
(

let uu____1614 = (

let uu____1616 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____1616))
in (match (uu____1614) with
| true -> begin
f
end
| uu____1621 -> begin
(

let uu____1623 = (reason1 ())
in (label uu____1623 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___363_1644 = g
in (

let uu____1645 = (

let uu____1646 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____1646))
in {FStar_TypeChecker_Env.guard_f = uu____1645; FStar_TypeChecker_Env.deferred = uu___363_1644.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___363_1644.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___363_1644.FStar_TypeChecker_Env.implicits}))
end))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____1667 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____1667) with
| true -> begin
c
end
| uu____1670 -> begin
(

let uu____1672 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____1672) with
| true -> begin
c
end
| uu____1675 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____1736 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1736)::[])
in (

let us = (

let uu____1758 = (

let uu____1761 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____1761)::[])
in (u_res)::uu____1758)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____1767 = (

let uu____1772 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____1773 = (

let uu____1774 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____1783 = (

let uu____1794 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____1803 = (

let uu____1814 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____1814)::[])
in (uu____1794)::uu____1803))
in (uu____1774)::uu____1783))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1772 uu____1773)))
in (uu____1767 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____1858 = (destruct_comp c1)
in (match (uu____1858) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end)))


let close_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____1894 -> (

let uu____1895 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (close_comp env bvs uu____1895)))))


let close_comp_if_refinement_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env t x c -> (

let t1 = (FStar_TypeChecker_Normalize.normalize_refinement FStar_TypeChecker_Normalize.whnf_steps env t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____1918; FStar_Syntax_Syntax.index = uu____1919; FStar_Syntax_Syntax.sort = {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____1921; FStar_Syntax_Syntax.vars = uu____1922}}, uu____1923) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____1931 -> begin
c
end)))


let should_not_inline_lc : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___343_1943 -> (match (uu___343_1943) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____1946 -> begin
false
end)))))


let should_return : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun env eopt lc -> (

let lc_is_unit = (

let uu____1971 = (

let uu____1974 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ FStar_Syntax_Util.arrow_formals_comp)
in (FStar_All.pipe_right uu____1974 FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____1971 (fun c -> ((

let uu____2030 = (FStar_TypeChecker_Env.is_reifiable_comp env c)
in (not (uu____2030))) && (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Util.is_unit)))))
in (match (eopt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (e) -> begin
((((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) && (not (lc_is_unit))) && (

let uu____2042 = (FStar_Syntax_Util.head_and_args' e)
in (match (uu____2042) with
| (head1, uu____2059) -> begin
(

let uu____2080 = (

let uu____2081 = (FStar_Syntax_Util.un_uinst head1)
in uu____2081.FStar_Syntax_Syntax.n)
in (match (uu____2080) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2086 = (

let uu____2088 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_irreducible env uu____2088))
in (not (uu____2086)))
end
| uu____2089 -> begin
true
end))
end))) && (

let uu____2092 = (should_not_inline_lc lc)
in (not (uu____2092))))
end)))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env u_t_opt t v1 -> (

let c = (

let uu____2120 = (

let uu____2122 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____2122))
in (match (uu____2120) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____2127 -> begin
(

let uu____2129 = (FStar_Syntax_Util.is_unit t)
in (match (uu____2129) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero)))
end
| uu____2132 -> begin
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

let uu____2138 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2138) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____2141 -> begin
(

let uu____2143 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____2143) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____2153 = (

let uu____2154 = (

let uu____2159 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2160 = (

let uu____2161 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____2170 = (

let uu____2181 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____2181)::[])
in (uu____2161)::uu____2170))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2159 uu____2160)))
in (uu____2154 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::[]) env uu____2153)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
end))
in ((

let uu____2217 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____2217) with
| true -> begin
(

let uu____2222 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____2224 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____2226 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2222 uu____2224 uu____2226))))
end
| uu____2229 -> begin
()
end));
c;
)))


let weaken_flags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags1 -> (

let uu____2243 = (FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___344_2249 -> (match (uu___344_2249) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____2252 -> begin
false
end))))
in (match (uu____2243) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____2257 -> begin
(FStar_All.pipe_right flags1 (FStar_List.collect (fun uu___345_2264 -> (match (uu___345_2264) with
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

let uu____2284 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____2284) with
| true -> begin
c
end
| uu____2287 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____2290 = (destruct_comp c1)
in (match (uu____2290) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____2304 = (

let uu____2309 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____2310 = (

let uu____2311 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____2320 = (

let uu____2331 = (FStar_Syntax_Syntax.as_arg formula)
in (

let uu____2340 = (

let uu____2351 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2351)::[])
in (uu____2331)::uu____2340))
in (uu____2311)::uu____2320))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2309 uu____2310)))
in (uu____2304 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (

let uu____2394 = (weaken_flags c1.FStar_Syntax_Syntax.flags)
in (mk_comp md u_res_t res_t wp1 uu____2394))))
end)))
end)))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____2418 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let uu____2420 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2420) with
| true -> begin
c
end
| uu____2423 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(weaken_comp env c f1)
end)
end))))
in (

let uu____2426 = (weaken_flags lc.FStar_Syntax_Syntax.cflags)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ uu____2426 weaken))))


let strengthen_comp : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun env reason c f flags1 -> (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____2471 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____2474 = (destruct_comp c1)
in (match (uu____2474) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____2488 = (

let uu____2493 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____2494 = (

let uu____2495 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____2504 = (

let uu____2515 = (

let uu____2524 = (

let uu____2525 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____2525 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2524))
in (

let uu____2534 = (

let uu____2545 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2545)::[])
in (uu____2515)::uu____2534))
in (uu____2495)::uu____2504))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2493 uu____2494)))
in (uu____2488 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 flags1)))
end)))
end))


let strengthen_precondition : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e_for_debugging_only lc g0 -> (

let uu____2633 = (FStar_TypeChecker_Env.is_trivial_guard_formula g0)
in (match (uu____2633) with
| true -> begin
((lc), (g0))
end
| uu____2640 -> begin
(

let flags1 = (

let uu____2645 = (

let uu____2653 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____2653) with
| true -> begin
((true), ((FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]))
end
| uu____2667 -> begin
((false), ([]))
end))
in (match (uu____2645) with
| (maybe_trivial_post, flags1) -> begin
(

let uu____2683 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___346_2691 -> (match (uu___346_2691) with
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
| uu____2694 -> begin
[]
end))))
in (FStar_List.append flags1 uu____2683))
end))
in (

let strengthen = (fun uu____2700 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____2703 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____2706 = (FStar_TypeChecker_Env.guard_form g01)
in (match (uu____2706) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____2709 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____2709) with
| true -> begin
(

let uu____2713 = (FStar_TypeChecker_Normalize.term_to_string env e_for_debugging_only)
in (

let uu____2715 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____2713 uu____2715)))
end
| uu____2718 -> begin
()
end));
(strengthen_comp env reason c f flags1);
)
end)))
end)))
in (

let uu____2720 = (

let uu____2721 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____2721 lc.FStar_Syntax_Syntax.res_typ flags1 strengthen))
in ((uu____2720), ((

let uu___364_2723 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___364_2723.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___364_2723.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___364_2723.FStar_TypeChecker_Env.implicits}))))))
end)))


let lcomp_has_trivial_postcondition : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) || (FStar_Util.for_some (fun uu___347_2732 -> (match (uu___347_2732) with
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
true
end
| uu____2736 -> begin
false
end)) lc.FStar_Syntax_Syntax.cflags)))


let maybe_add_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env uopt lc e -> (

let uu____2765 = ((FStar_Syntax_Util.is_lcomp_partial_return lc) || env.FStar_TypeChecker_Env.lax)
in (match (uu____2765) with
| true -> begin
e
end
| uu____2770 -> begin
(

let uu____2772 = ((lcomp_has_trivial_postcondition lc) && (

let uu____2775 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____2775)))
in (match (uu____2772) with
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
| uu____2799 -> begin
e
end))
end)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____2828 -> (match (uu____2828) with
| (b, lc2) -> begin
(

let debug1 = (fun f -> (

let uu____2848 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____2848) with
| true -> begin
(f ())
end
| uu____2853 -> begin
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

let uu____2861 = ((should_not_inline_lc lc11) || (should_not_inline_lc lc21))
in (match (uu____2861) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____2866 -> begin
(

let flags1 = (

let uu____2871 = (FStar_Syntax_Util.is_total_lcomp lc11)
in (match (uu____2871) with
| true -> begin
(

let uu____2876 = (FStar_Syntax_Util.is_total_lcomp lc21)
in (match (uu____2876) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____2881 -> begin
(

let uu____2883 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
in (match (uu____2883) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____2888 -> begin
[]
end))
end))
end
| uu____2890 -> begin
(

let uu____2892 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) && (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21))
in (match (uu____2892) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____2897 -> begin
[]
end))
end))
in (

let uu____2899 = (lcomp_has_trivial_postcondition lc21)
in (match (uu____2899) with
| true -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::flags1
end
| uu____2904 -> begin
flags1
end)))
end))
in (

let bind_it = (fun uu____2911 -> (

let uu____2912 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2912) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____2916 -> begin
(

let c1 = (FStar_Syntax_Syntax.lcomp_comp lc11)
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp lc21)
in ((debug1 (fun uu____2929 -> (

let uu____2930 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____2932 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____2937 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n" uu____2930 uu____2932 uu____2937))))));
(

let aux = (fun uu____2955 -> (

let uu____2956 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____2956) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____2987) -> begin
(

let uu____2988 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____2988) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____3009 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____3018 -> begin
(

let uu____3020 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____3020) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____3041 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let try_simplify = (fun uu____3065 -> (

let uu____3066 = (

let uu____3068 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____3068))
in (match (uu____3066) with
| true -> begin
(

let uu____3082 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3082) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____3103 -> begin
(

let uu____3105 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonTrivialPreConditionInPrims), ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")) uu____3105))
end))
end
| uu____3118 -> begin
(

let uu____3120 = (FStar_Syntax_Util.is_total_comp c1)
in (match (uu____3120) with
| true -> begin
(

let close1 = (fun x reason c -> (

let x1 = (

let uu___365_3162 = x
in {FStar_Syntax_Syntax.ppname = uu___365_3162.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___365_3162.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____3163 = (

let uu____3169 = (close_comp_if_refinement_t env x1.FStar_Syntax_Syntax.sort x1 c)
in ((uu____3169), (reason)))
in FStar_Util.Inl (uu____3163))))
in (match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____3205 = (FStar_All.pipe_right c2 (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[])))
in (FStar_All.pipe_right uu____3205 (close1 x "c1 Tot")))
end
| (uu____3219, FStar_Pervasives_Native.Some (x)) -> begin
(FStar_All.pipe_right c2 (close1 x "c1 Tot only close"))
end
| (uu____3242, uu____3243) -> begin
(aux ())
end))
end
| uu____3256 -> begin
(

let uu____3258 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3258) with
| true -> begin
(

let uu____3271 = (

let uu____3277 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____3277), ("both GTot")))
in FStar_Util.Inl (uu____3271))
end
| uu____3286 -> begin
(aux ())
end))
end))
end)))
in (

let uu____3288 = (try_simplify ())
in (match (uu____3288) with
| FStar_Util.Inl (c, reason) -> begin
((debug1 (fun uu____3314 -> (

let uu____3315 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "(2) bind: Simplified (because %s) to\n\t%s\n" reason uu____3315))));
c;
)
end
| FStar_Util.Inr (reason) -> begin
((debug1 (fun uu____3329 -> (FStar_Util.print1 "(2) bind: Not simplified because %s\n" reason)));
(

let mk_bind = (fun c11 b1 c21 -> (

let uu____3351 = (lift_and_destruct env c11 c21)
in (match (uu____3351) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b1) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3404 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____3404)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____3424 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3424)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____3471 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____3480 = (

let uu____3491 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3500 = (

let uu____3511 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____3520 = (

let uu____3531 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____3540 = (

let uu____3551 = (

let uu____3560 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____3560))
in (uu____3551)::[])
in (uu____3531)::uu____3540))
in (uu____3511)::uu____3520))
in (uu____3491)::uu____3500))
in (uu____3471)::uu____3480))
in (

let wp = (

let uu____3612 = (

let uu____3617 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3617 wp_args))
in (uu____3612 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (mk_comp md u_t2 t2 wp bind_flags))))))
end)))
in (

let mk_seq = (fun c11 b1 c21 -> (

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in (

let uu____3642 = (FStar_TypeChecker_Env.join env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____3642) with
| (m, uu____3650, lift2) -> begin
(

let c23 = (

let uu____3653 = (lift_comp c22 m lift2)
in (FStar_Syntax_Syntax.mk_Comp uu____3653))
in (

let uu____3654 = (destruct_comp c12)
in (match (uu____3654) with
| (u1, t1, wp1) -> begin
(

let md_pure_or_ghost = (FStar_TypeChecker_Env.get_effect_decl env c12.FStar_Syntax_Syntax.effect_name)
in (

let vc1 = (

let uu____3668 = (

let uu____3673 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u1)::[]) env md_pure_or_ghost md_pure_or_ghost.FStar_Syntax_Syntax.trivial)
in (

let uu____3674 = (

let uu____3675 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3684 = (

let uu____3695 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____3695)::[])
in (uu____3675)::uu____3684))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3673 uu____3674)))
in (uu____3668 FStar_Pervasives_Native.None r1))
in (strengthen_comp env FStar_Pervasives_Native.None c23 vc1 bind_flags)))
end)))
end)))))
in (

let c1_typ = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____3735 = (destruct_comp c1_typ)
in (match (uu____3735) with
| (u_res_t1, res_t1, uu____3744) -> begin
(

let uu____3745 = ((FStar_Option.isSome b) && (should_return env e1opt lc11))
in (match (uu____3745) with
| true -> begin
(

let e1 = (FStar_Option.get e1opt)
in (

let x = (FStar_Option.get b)
in (

let uu____3750 = (FStar_Syntax_Util.is_partial_return c1)
in (match (uu____3750) with
| true -> begin
((debug1 (fun uu____3760 -> (

let uu____3761 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____3763 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case a): Substituting %s for %s" uu____3761 uu____3763)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (mk_bind c1 b c21));
)
end
| uu____3769 -> begin
(

let uu____3771 = (((FStar_Options.vcgen_optimize_bind_as_seq ()) && (lcomp_has_trivial_postcondition lc11)) && (

let uu____3774 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____3774)))
in (match (uu____3771) with
| true -> begin
(

let e1' = (

let uu____3795 = (FStar_Options.vcgen_decorate_with_type ())
in (match (uu____3795) with
| true -> begin
(FStar_Syntax_Util.mk_with_type u_res_t1 res_t1 e1)
end
| uu____3798 -> begin
e1
end))
in ((debug1 (fun uu____3807 -> (

let uu____3808 = (FStar_TypeChecker_Normalize.term_to_string env e1')
in (

let uu____3810 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case b): Substituting %s for %s" uu____3808 uu____3810)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1'))))::[]) c2)
in (mk_seq c1 b c21));
))
end
| uu____3816 -> begin
((debug1 (fun uu____3825 -> (

let uu____3826 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____3828 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case c): Adding equality %s = %s" uu____3826 uu____3828)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (

let x_eq_e = (

let uu____3835 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq2 u_res_t1 res_t1 e1 uu____3835))
in (

let c22 = (weaken_comp env c21 x_eq_e)
in (mk_bind c1 b c22))));
)
end))
end))))
end
| uu____3837 -> begin
(mk_bind c1 b c2)
end))
end)))));
)
end))));
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
| uu____3853 -> begin
g2
end))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let should_return1 = ((((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)) && (should_return env (FStar_Pervasives_Native.Some (e)) lc)) && (

let uu____3877 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____3877))))
in (

let flags1 = (match (should_return1) with
| true -> begin
(

let uu____3885 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____3885) with
| true -> begin
(FStar_Syntax_Syntax.RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____3890 -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end))
end
| uu____3892 -> begin
lc.FStar_Syntax_Syntax.cflags
end)
in (

let refine1 = (fun uu____3901 -> (

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

let uu____3905 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____3905) with
| true -> begin
(

let retc = (return_value env (FStar_Pervasives_Native.Some (u_t)) (FStar_Syntax_Util.comp_result c) e)
in (

let uu____3911 = (

let uu____3913 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____3913)))
in (match (uu____3911) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___366_3920 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___366_3920.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___366_3920.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___366_3920.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags1})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____3921 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags1)
end)))
end
| uu____3923 -> begin
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

let uu____3933 = (

let uu____3934 = (return_value env (FStar_Pervasives_Native.Some (u_t)) t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____3934 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3933))
in (

let eq1 = (FStar_Syntax_Util.mk_eq2 u_t t xexp e)
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____3937 = (

let uu____3938 = (

let uu____3939 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None uu____3939 ((FStar_Pervasives_Native.Some (x)), (eq_ret))))
in (FStar_Syntax_Syntax.lcomp_comp uu____3938))
in (FStar_Syntax_Util.comp_set_flags uu____3937 flags1))))))))))
end)))))
in (match ((not (should_return1))) with
| true -> begin
lc
end
| uu____3943 -> begin
(FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ flags1 refine1)
end)))))


let maybe_return_e2_and_bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r env e1opt lc1 e2 uu____3977 -> (match (uu____3977) with
| (x, lc2) -> begin
(

let lc21 = (

let eff1 = (FStar_TypeChecker_Env.norm_eff_name env lc1.FStar_Syntax_Syntax.eff_name)
in (

let eff2 = (FStar_TypeChecker_Env.norm_eff_name env lc2.FStar_Syntax_Syntax.eff_name)
in (

let uu____3989 = (((

let uu____3993 = (is_pure_or_ghost_effect env eff1)
in (not (uu____3993))) || (should_not_inline_lc lc1)) && (is_pure_or_ghost_effect env eff2))
in (match (uu____3989) with
| true -> begin
(maybe_assume_result_eq_pure_term env e2 lc2)
end
| uu____3996 -> begin
lc2
end))))
in (bind r env e1opt lc1 ((x), (lc21))))
end))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____4011 = (

let uu____4012 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____4012))
in (FStar_Syntax_Syntax.fvar uu____4011 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp)) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____4082 -> (match (uu____4082) with
| (uu____4096, eff_label, uu____4098, uu____4099) -> begin
(join_effects env eff eff_label)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let uu____4112 = (

let uu____4120 = (FStar_All.pipe_right lcases (FStar_Util.for_some (fun uu____4158 -> (match (uu____4158) with
| (uu____4173, uu____4174, flags1, uu____4176) -> begin
(FStar_All.pipe_right flags1 (FStar_Util.for_some (fun uu___348_4193 -> (match (uu___348_4193) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____4196 -> begin
false
end))))
end))))
in (match (uu____4120) with
| true -> begin
((true), ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
end
| uu____4210 -> begin
((false), ([]))
end))
in (match (uu____4112) with
| (should_not_inline_whole_match, bind_cases_flags) -> begin
(

let bind_cases = (fun uu____4229 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____4231 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4231) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____4234 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____4272 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____4273 = (

let uu____4278 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____4279 = (

let uu____4280 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____4289 = (

let uu____4300 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____4309 = (

let uu____4320 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____4329 = (

let uu____4340 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____4340)::[])
in (uu____4320)::uu____4329))
in (uu____4300)::uu____4309))
in (uu____4280)::uu____4289))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4278 uu____4279)))
in (uu____4273 FStar_Pervasives_Native.None uu____4272))))
in (

let default_case = (

let post_k = (

let uu____4395 = (

let uu____4404 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____4404)::[])
in (

let uu____4423 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____4395 uu____4423)))
in (

let kwp = (

let uu____4429 = (

let uu____4438 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____4438)::[])
in (

let uu____4457 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____4429 uu____4457)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____4464 = (

let uu____4465 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____4465)::[])
in (

let uu____4484 = (

let uu____4487 = (

let uu____4494 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____4494))
in (

let uu____4495 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____4487 uu____4495)))
in (FStar_Syntax_Util.abs uu____4464 uu____4484 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let maybe_return = (fun eff_label_then cthen -> (

let uu____4519 = (should_not_inline_whole_match || (

let uu____4522 = (is_pure_or_ghost_effect env eff)
in (not (uu____4522))))
in (match (uu____4519) with
| true -> begin
(cthen true)
end
| uu____4526 -> begin
(cthen false)
end)))
in (

let comp = (FStar_List.fold_right (fun uu____4561 celse -> (match (uu____4561) with
| (g, eff_label, uu____4578, cthen) -> begin
(

let uu____4592 = (

let uu____4617 = (

let uu____4618 = (maybe_return eff_label cthen)
in (FStar_Syntax_Syntax.lcomp_comp uu____4618))
in (lift_and_destruct env uu____4617 celse))
in (match (uu____4592) with
| ((md, uu____4620, uu____4621), (uu____4622, uu____4623, wp_then), (uu____4625, uu____4626, wp_else)) -> begin
(

let uu____4646 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____4646 []))
end))
end)) lcases default_case)
in (match (lcases) with
| [] -> begin
comp
end
| (uu____4661)::[] -> begin
comp
end
| uu____4704 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____4723 = (destruct_comp comp1)
in (match (uu____4723) with
| (uu____4730, uu____4731, wp) -> begin
(

let wp1 = (

let uu____4736 = (

let uu____4741 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____4742 = (

let uu____4743 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4752 = (

let uu____4763 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4763)::[])
in (uu____4743)::uu____4752))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4741 uu____4742)))
in (uu____4736 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 bind_cases_flags))
end))))
end)))))
end))))
in (FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags bind_cases))
end))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____4831 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____4831) with
| FStar_Pervasives_Native.None -> begin
(match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(

let uu____4847 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq env e c c')
in (

let uu____4853 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____4847 uu____4853)))
end
| uu____4860 -> begin
(

let uu____4862 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____4868 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____4862 uu____4868)))
end)
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let universe_of_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe = (fun env u_res c -> (

let c_lid = (

let uu____4893 = (FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name)
in (FStar_All.pipe_right uu____4893 (FStar_TypeChecker_Env.norm_eff_name env)))
in (

let uu____4896 = (FStar_Syntax_Util.is_pure_or_ghost_effect c_lid)
in (match (uu____4896) with
| true -> begin
u_res
end
| uu____4899 -> begin
(

let is_total = (

let uu____4903 = (FStar_TypeChecker_Env.lookup_effect_quals env c_lid)
in (FStar_All.pipe_right uu____4903 (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.TotalEffect)))))
in (match ((not (is_total))) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____4912 -> begin
(

let uu____4914 = (FStar_TypeChecker_Env.effect_repr env c u_res)
in (match (uu____4914) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4917 = (

let uu____4923 = (

let uu____4925 = (FStar_Syntax_Print.lid_to_string c_lid)
in (FStar_Util.format1 "Effect %s is marked total but does not have a repr" uu____4925))
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____4923)))
in (FStar_Errors.raise_error uu____4917 c.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
end))
end))))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match (env.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
((e), (lc))
end
| uu____4960 -> begin
(

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____4970 = (

let uu____4971 = (FStar_Syntax_Subst.compress t2)
in uu____4971.FStar_Syntax_Syntax.n)
in (match (uu____4970) with
| FStar_Syntax_Syntax.Tm_type (uu____4975) -> begin
true
end
| uu____4977 -> begin
false
end))))
in (

let uu____4979 = (

let uu____4980 = (FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ)
in uu____4980.FStar_Syntax_Syntax.n)
in (match (uu____4979) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____4988 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (

let uu____4998 = (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____4998 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let lc1 = (

let uu____5001 = (

let uu____5002 = (

let uu____5003 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5003))
in ((FStar_Pervasives_Native.None), (uu____5002)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____5001))
in (

let e1 = (

let uu____5009 = (

let uu____5014 = (

let uu____5015 = (FStar_Syntax_Syntax.as_arg e)
in (uu____5015)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5014))
in (uu____5009 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____5042 -> begin
((e), (lc))
end)))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> ((

let uu____5077 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5077) with
| true -> begin
(

let uu____5080 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5082 = (FStar_Syntax_Print.lcomp_to_string lc)
in (

let uu____5084 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n" uu____5080 uu____5082 uu____5084))))
end
| uu____5087 -> begin
()
end));
(

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____5094 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____5094) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____5119 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____5145 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5145), (false)))
end
| uu____5153 -> begin
(

let uu____5155 = (FStar_TypeChecker_Rel.get_subtyping_predicate env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5155), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____5168) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____5180 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Errors.raise_error uu____5180 e.FStar_Syntax_Syntax.pos))
end
| uu____5192 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___367_5196 = lc
in {FStar_Syntax_Syntax.eff_name = uu___367_5196.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___367_5196.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___367_5196.FStar_Syntax_Syntax.comp_thunk})), (FStar_TypeChecker_Env.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____5203 = (FStar_TypeChecker_Env.guard_form g)
in (match (uu____5203) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let strengthen_trivial = (fun uu____5215 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let set_result_typ1 = (fun c1 -> (FStar_Syntax_Util.set_result_typ c1 t))
in (

let uu____5226 = (

let uu____5228 = (FStar_Syntax_Util.eq_tm t res_t)
in (Prims.op_Equality uu____5228 FStar_Syntax_Util.Equal))
in (match (uu____5226) with
| true -> begin
((

let uu____5231 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5231) with
| true -> begin
(

let uu____5235 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____5237 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n" uu____5235 uu____5237)))
end
| uu____5240 -> begin
()
end));
(set_result_typ1 c);
)
end
| uu____5242 -> begin
(

let is_res_t_refinement = (

let res_t1 = (FStar_TypeChecker_Normalize.normalize_refinement FStar_TypeChecker_Normalize.whnf_steps env res_t)
in (match (res_t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (uu____5248) -> begin
true
end
| uu____5256 -> begin
false
end))
in (match (is_res_t_refinement) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (res_t.FStar_Syntax_Syntax.pos)) res_t)
in (

let cret = (

let uu____5261 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env (comp_univ_opt c) res_t uu____5261))
in (

let lc1 = (

let uu____5263 = (FStar_Syntax_Util.lcomp_of_comp c)
in (

let uu____5264 = (

let uu____5265 = (FStar_Syntax_Util.lcomp_of_comp cret)
in ((FStar_Pervasives_Native.Some (x)), (uu____5265)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____5263 uu____5264)))
in ((

let uu____5269 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5269) with
| true -> begin
(

let uu____5273 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5275 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____5277 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____5279 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (FStar_Util.print4 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n" uu____5273 uu____5275 uu____5277 uu____5279)))))
end
| uu____5282 -> begin
()
end));
(

let uu____5284 = (FStar_Syntax_Syntax.lcomp_comp lc1)
in (set_result_typ1 uu____5284));
))))
end
| uu____5285 -> begin
((

let uu____5288 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5288) with
| true -> begin
(

let uu____5292 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____5294 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n" uu____5292 uu____5294)))
end
| uu____5297 -> begin
()
end));
(set_result_typ1 c);
)
end))
end))))))
in (

let lc1 = (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags strengthen_trivial)
in ((e), (lc1), (g))))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___368_5302 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___368_5302.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___368_5302.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___368_5302.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____5308 -> (

let uu____5309 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5309) with
| true -> begin
(FStar_Syntax_Syntax.lcomp_comp lc)
end
| uu____5312 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::[]) env f)
in (

let uu____5315 = (

let uu____5316 = (FStar_Syntax_Subst.compress f1)
in uu____5316.FStar_Syntax_Syntax.n)
in (match (uu____5315) with
| FStar_Syntax_Syntax.Tm_abs (uu____5319, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5321; FStar_Syntax_Syntax.vars = uu____5322}, uu____5323) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___369_5349 = lc
in {FStar_Syntax_Syntax.eff_name = uu___369_5349.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___369_5349.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___369_5349.FStar_Syntax_Syntax.comp_thunk})
in (FStar_Syntax_Syntax.lcomp_comp lc1))
end
| uu____5350 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((

let uu____5353 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5353) with
| true -> begin
(

let uu____5357 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____5359 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____5361 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____5363 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____5357 uu____5359 uu____5361 uu____5363)))))
end
| uu____5366 -> begin
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

let uu____5376 = (

let uu____5381 = (

let uu____5382 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____5382)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____5381))
in (uu____5376 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____5409 -> begin
f1
end)
in (

let uu____5411 = (

let uu____5416 = (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____5437 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____5438 = (FStar_Syntax_Util.lcomp_of_comp cret)
in (

let uu____5439 = (FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____5416 uu____5437 e uu____5438 uu____5439)))))
in (match (uu____5411) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___370_5443 = x
in {FStar_Syntax_Syntax.ppname = uu___370_5443.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___370_5443.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____5445 = (FStar_Syntax_Util.lcomp_of_comp c)
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____5445 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((

let uu____5450 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5450) with
| true -> begin
(

let uu____5454 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____5454))
end
| uu____5457 -> begin
()
end));
c2;
))))
end)))))));
))
end)))
end)))
in (

let flags1 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___349_5467 -> (match (uu___349_5467) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____5470 -> begin
[]
end))))
in (

let lc1 = (

let uu____5472 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____5472 t flags1 strengthen))
in (

let g2 = (

let uu___371_5474 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___371_5474.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___371_5474.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___371_5474.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end)));
))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____5510 = (

let uu____5513 = (

let uu____5518 = (

let uu____5519 = (

let uu____5528 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____5528))
in (uu____5519)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____5518))
in (uu____5513 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____5510))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env t))
in (

let uu____5553 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____5553) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____5564 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____5572) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____5588) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____5605 = ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))
in (match (uu____5605) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____5621))::((ens, uu____5623))::uu____5624 -> begin
(

let uu____5667 = (

let uu____5670 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____5670))
in (

let uu____5671 = (

let uu____5672 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____5672))
in ((uu____5667), (uu____5671))))
end
| uu____5675 -> begin
(

let uu____5686 = (

let uu____5692 = (

let uu____5694 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____5694))
in ((FStar_Errors.Fatal_EffectConstructorNotFullyApplied), (uu____5692)))
in (FStar_Errors.raise_error uu____5686 comp.FStar_Syntax_Syntax.pos))
end)
end
| uu____5704 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____5714))::uu____5715 -> begin
(

let uu____5742 = (

let uu____5747 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5747))
in (match (uu____5742) with
| (us_r, uu____5779) -> begin
(

let uu____5780 = (

let uu____5785 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5785))
in (match (uu____5780) with
| (us_e, uu____5817) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____5820 = (

let uu____5821 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar uu____5821 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5820 us_r))
in (

let as_ens = (

let uu____5823 = (

let uu____5824 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar uu____5824 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5823 us_e))
in (

let req = (

let uu____5828 = (

let uu____5833 = (

let uu____5834 = (

let uu____5845 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5845)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____5834)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____5833))
in (uu____5828 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____5887 = (

let uu____5892 = (

let uu____5893 = (

let uu____5904 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5904)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____5893)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____5892))
in (uu____5887 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____5943 = (

let uu____5946 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____5946))
in (

let uu____5947 = (

let uu____5948 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____5948))
in ((uu____5943), (uu____5947)))))))))
end))
end))
end
| uu____5951 -> begin
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

let uu____5985 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____5985) with
| true -> begin
(

let uu____5990 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____5992 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____5990 uu____5992)))
end
| uu____5995 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____6046 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6046) with
| true -> begin
(

let uu____6051 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6053 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6051 uu____6053)))
end
| uu____6056 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____6064 = (

let uu____6066 = (

let uu____6067 = (FStar_Syntax_Subst.compress t)
in uu____6067.FStar_Syntax_Syntax.n)
in (match (uu____6066) with
| FStar_Syntax_Syntax.Tm_app (uu____6071) -> begin
false
end
| uu____6089 -> begin
true
end))
in (match (uu____6064) with
| true -> begin
t
end
| uu____6092 -> begin
(

let uu____6094 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6094) with
| (head1, args) -> begin
(

let uu____6137 = (

let uu____6139 = (

let uu____6140 = (FStar_Syntax_Subst.compress head1)
in uu____6140.FStar_Syntax_Syntax.n)
in (match (uu____6139) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____6145 -> begin
false
end))
in (match (uu____6137) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____6177 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____6189 -> begin
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
| uu____6221 -> begin
((

let uu____6224 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6224) with
| true -> begin
(

let uu____6227 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6229 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____6231 = (

let uu____6233 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Common.string_of_option FStar_Syntax_Print.term_to_string uu____6233))
in (FStar_Util.print3 "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n" uu____6227 uu____6229 uu____6231))))
end
| uu____6237 -> begin
()
end));
(

let number_of_implicits = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____6246 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____6246) with
| (formals, uu____6262) -> begin
(

let n_implicits = (

let uu____6284 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____6362 -> (match (uu____6362) with
| (uu____6370, imp) -> begin
((FStar_Option.isNone imp) || (

let uu____6377 = (FStar_Syntax_Util.eq_aqual imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)))
in (Prims.op_Equality uu____6377 FStar_Syntax_Util.Equal)))
end))))
in (match (uu____6284) with
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

let uu____6504 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6504) with
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

let uu____6532 = (

let uu____6538 = (

let uu____6540 = (FStar_Util.string_of_int n_expected)
in (

let uu____6548 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6550 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____6540 uu____6548 uu____6550))))
in ((FStar_Errors.Fatal_MissingImplicitArguments), (uu____6538)))
in (

let uu____6560 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____6532 uu____6560)))
end
| uu____6564 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___350_6588 -> (match (uu___350_6588) with
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

let uu____6631 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6631) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_0_2), uu____6749) when (_0_2 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Env.trivial_guard))
end
| (uu____6794, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6796))))::rest) -> begin
(

let t2 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____6830 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t2)
in (match (uu____6830) with
| (v1, uu____6871, g) -> begin
((

let uu____6886 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6886) with
| true -> begin
(

let uu____6889 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.print1 "maybe_instantiate: Instantiating implicit with %s\n" uu____6889))
end
| uu____6892 -> begin
()
end));
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____6899 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____6899) with
| (args, bs3, subst3, g') -> begin
(

let uu____6992 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::args), (bs3), (subst3), (uu____6992)))
end)));
)
end)))
end
| (uu____7019, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau))))::rest) -> begin
(

let t2 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____7056 = (

let uu____7069 = (

let uu____7076 = (

let uu____7081 = (FStar_Dyn.mkdyn env)
in ((uu____7081), (tau)))
in FStar_Pervasives_Native.Some (uu____7076))
in (FStar_TypeChecker_Env.new_implicit_var_aux "Instantiation of meta argument" e.FStar_Syntax_Syntax.pos env t2 FStar_Syntax_Syntax.Strict uu____7069))
in (match (uu____7056) with
| (v1, uu____7114, g) -> begin
((

let uu____7129 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7129) with
| true -> begin
(

let uu____7132 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.print1 "maybe_instantiate: Instantiating meta argument with %s\n" uu____7132))
end
| uu____7135 -> begin
()
end));
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____7142 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____7142) with
| (args, bs3, subst3, g') -> begin
(

let uu____7235 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::args), (bs3), (subst3), (uu____7235)))
end)));
)
end)))
end
| (uu____7262, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Env.trivial_guard))
end))
in (

let uu____7310 = (

let uu____7337 = (inst_n_binders t1)
in (aux [] uu____7337 bs1))
in (match (uu____7310) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____7409) -> begin
((e), (torig), (guard))
end
| (uu____7440, []) when (

let uu____7471 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____7471))) -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____7473 -> begin
(

let t2 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____7501 -> begin
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
| uu____7514 -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end)))));
)
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____7526 = (

let uu____7530 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____7530 (FStar_List.map (fun u -> (

let uu____7542 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____7542 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____7526 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____7570 = (FStar_Util.set_is_empty x)
in (match (uu____7570) with
| true -> begin
[]
end
| uu____7575 -> begin
(

let s = (

let uu____7588 = (

let uu____7591 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____7591))
in (FStar_All.pipe_right uu____7588 FStar_Util.set_elements))
in ((

let uu____7607 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7607) with
| true -> begin
(

let uu____7612 = (

let uu____7614 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____7614))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____7612))
end
| uu____7618 -> begin
()
end));
(

let r = (

let uu____7623 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____7623))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____7662 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7662) with
| true -> begin
(

let uu____7667 = (

let uu____7669 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7669))
in (

let uu____7673 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____7675 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____7667 uu____7673 uu____7675))))
end
| uu____7678 -> begin
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

let uu____7705 = (FStar_Util.set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____7705 FStar_Util.set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____7744) -> begin
generalized_univ_names
end
| (uu____7751, []) -> begin
explicit_univ_names
end
| uu____7758 -> begin
(

let uu____7767 = (

let uu____7773 = (

let uu____7775 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " uu____7775))
in ((FStar_Errors.Fatal_UnexpectedGeneralizedUniverse), (uu____7773)))
in (FStar_Errors.raise_error uu____7767 t.FStar_Syntax_Syntax.pos))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in ((

let uu____7797 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7797) with
| true -> begin
(

let uu____7802 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____7804 = (FStar_Syntax_Print.univ_names_to_string univnames1)
in (FStar_Util.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" uu____7802 uu____7804)))
end
| uu____7807 -> begin
()
end));
(

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____7813 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7813) with
| true -> begin
(

let uu____7818 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____7818))
end
| uu____7821 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____7827 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7827) with
| true -> begin
(

let uu____7832 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____7834 = (FStar_Syntax_Print.univ_names_to_string gen1)
in (FStar_Util.print2 "After generalization, t: %s and univs: %s\n" uu____7832 uu____7834)))
end
| uu____7837 -> begin
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

let uu____7918 = (

let uu____7920 = (FStar_Util.for_all (fun uu____7934 -> (match (uu____7934) with
| (uu____7944, uu____7945, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____7920))
in (match (uu____7918) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7988 -> begin
(

let norm1 = (fun c -> ((

let uu____7997 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____7997) with
| true -> begin
(

let uu____8000 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____8000))
end
| uu____8003 -> begin
()
end));
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env c)
in ((

let uu____8007 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____8007) with
| true -> begin
(

let uu____8010 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8010))
end
| uu____8013 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____8028 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____8028 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____8062 -> (match (uu____8062) with
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

let uu____8099 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8099) with
| true -> begin
(

let uu____8104 = (

let uu____8106 = (

let uu____8110 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____8110 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8106 (FStar_String.concat ", ")))
in (

let uu____8158 = (

let uu____8160 = (

let uu____8164 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____8164 (FStar_List.map (fun u -> (

let uu____8177 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____8179 = (FStar_Syntax_Print.term_to_string u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____8177 uu____8179)))))))
in (FStar_All.pipe_right uu____8160 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8104 uu____8158)))
end
| uu____8188 -> begin
()
end));
(

let univs2 = (

let uu____8193 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uv -> (

let uu____8205 = (FStar_Syntax_Free.univs uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.set_union univs2 uu____8205))) univs1 uu____8193))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____8212 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8212) with
| true -> begin
(

let uu____8217 = (

let uu____8219 = (

let uu____8223 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____8223 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8219 (FStar_String.concat ", ")))
in (

let uu____8271 = (

let uu____8273 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> (

let uu____8287 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____8289 = (FStar_TypeChecker_Normalize.term_to_string env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____8287 uu____8289))))))
in (FStar_All.pipe_right uu____8273 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8217 uu____8271)))
end
| uu____8298 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
)))))
end))
in (

let uu____8310 = (

let uu____8327 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____8327))
in (match (uu____8310) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____8417 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____8417) with
| true -> begin
()
end
| uu____8420 -> begin
(

let uu____8422 = lec_hd
in (match (uu____8422) with
| (lb1, uu____8430, uu____8431) -> begin
(

let uu____8432 = lec2
in (match (uu____8432) with
| (lb2, uu____8440, uu____8441) -> begin
(

let msg = (

let uu____8444 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8446 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____8444 uu____8446)))
in (

let uu____8449 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleSetOfUniverse), (msg)) uu____8449)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun u -> (FStar_All.pipe_right u21 (FStar_Util.for_some (fun u' -> (FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head u'.FStar_Syntax_Syntax.ctx_uvar_head))))))))
in (

let uu____8517 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____8517) with
| true -> begin
()
end
| uu____8520 -> begin
(

let uu____8522 = lec_hd
in (match (uu____8522) with
| (lb1, uu____8530, uu____8531) -> begin
(

let uu____8532 = lec2
in (match (uu____8532) with
| (lb2, uu____8540, uu____8541) -> begin
(

let msg = (

let uu____8544 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8546 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____8544 uu____8546)))
in (

let uu____8549 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleNumberOfTypes), (msg)) uu____8549)))
end))
end))
end))))
in (

let lecs1 = (

let uu____8560 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____8613 = (univs_and_uvars_of_lec this_lec)
in (match (uu____8613) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____8560 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail1 = (fun k -> (

let uu____8718 = lec_hd
in (match (uu____8718) with
| (lbname, e, c) -> begin
(

let uu____8728 = (

let uu____8734 = (

let uu____8736 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____8738 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____8740 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____8736 uu____8738 uu____8740))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____8734)))
in (

let uu____8744 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____8728 uu____8744)))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun u -> (

let uu____8763 = (FStar_Syntax_Unionfind.find u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____8763) with
| FStar_Pervasives_Native.Some (uu____8772) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____8780 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____8784 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8784) with
| (bs, kres) -> begin
((

let uu____8828 = (

let uu____8829 = (

let uu____8832 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____8832))
in uu____8829.FStar_Syntax_Syntax.n)
in (match (uu____8828) with
| FStar_Syntax_Syntax.Tm_type (uu____8833) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____8837 = (

let uu____8839 = (FStar_Util.set_is_empty free)
in (not (uu____8839)))
in (match (uu____8837) with
| true -> begin
(fail1 kres)
end
| uu____8842 -> begin
()
end)))
end
| uu____8844 -> begin
(fail1 kres)
end));
(

let a = (

let uu____8846 = (

let uu____8849 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_3 -> FStar_Pervasives_Native.Some (_0_3)) uu____8849))
in (FStar_Syntax_Syntax.new_bv uu____8846 kres))
in (

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Syntax.bv_to_name a)
end
| uu____8859 -> begin
(

let uu____8868 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____8868 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
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

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____8971 -> (match (uu____8971) with
| (lbname, e, c) -> begin
(

let uu____9017 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____9078 -> begin
(

let uu____9091 = ((e), (c))
in (match (uu____9091) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____9131 -> (match (uu____9131) with
| (x, uu____9137) -> begin
(

let uu____9138 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____9138))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____9156 = (

let uu____9158 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____9158))
in (match (uu____9156) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____9162 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____9164 -> begin
e1
end)
in (

let t = (

let uu____9167 = (

let uu____9168 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____9168.FStar_Syntax_Syntax.n)
in (match (uu____9167) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____9193 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____9193) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____9204 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____9208 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____9208), (gen_tvars))))))))
end))
end)
in (match (uu____9017) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____9355 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____9355) with
| true -> begin
(

let uu____9358 = (

let uu____9360 = (FStar_List.map (fun uu____9375 -> (match (uu____9375) with
| (lb, uu____9384, uu____9385) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____9360 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____9358))
end
| uu____9392 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____9411 -> (match (uu____9411) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____9440 = (gen env is_rec lecs)
in (match (uu____9440) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____9539 -> (match (uu____9539) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____9601 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____9601) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____9649 -> (match (uu____9649) with
| (l, us, e, c, gvs) -> begin
(

let uu____9683 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____9685 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____9687 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____9689 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____9691 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____9683 uu____9685 uu____9687 uu____9689 uu____9691))))))
end))))
end
| uu____9695 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____9736 -> (match (uu____9736) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____9780 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____9780), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check1 = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____9839 -> begin
(

let uu____9841 = (FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21)
in (match (uu____9841) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____9847 = (FStar_TypeChecker_Env.apply_guard f e)
in (FStar_All.pipe_left (fun _0_4 -> FStar_Pervasives_Native.Some (_0_4)) uu____9847))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____9857 = (

let uu____9858 = (FStar_Syntax_Subst.compress e1)
in uu____9858.FStar_Syntax_Syntax.n)
in (match (uu____9857) with
| FStar_Syntax_Syntax.Tm_name (uu____9862) -> begin
true
end
| uu____9864 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___372_9885 = x
in {FStar_Syntax_Syntax.ppname = uu___372_9885.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___372_9885.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____9886 -> begin
e2
end)))
in (

let env2 = (

let uu___373_9888 = env1
in (

let uu____9889 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___373_9888.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___373_9888.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___373_9888.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___373_9888.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___373_9888.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___373_9888.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___373_9888.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___373_9888.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___373_9888.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___373_9888.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___373_9888.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___373_9888.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___373_9888.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___373_9888.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___373_9888.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___373_9888.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___373_9888.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____9889; FStar_TypeChecker_Env.is_iface = uu___373_9888.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___373_9888.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___373_9888.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___373_9888.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___373_9888.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___373_9888.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___373_9888.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___373_9888.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___373_9888.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___373_9888.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___373_9888.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___373_9888.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___373_9888.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___373_9888.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___373_9888.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___373_9888.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___373_9888.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___373_9888.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___373_9888.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___373_9888.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___373_9888.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___373_9888.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___373_9888.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___373_9888.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___373_9888.FStar_TypeChecker_Env.nbe}))
in (

let uu____9891 = (check1 env2 t1 t2)
in (match (uu____9891) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9898 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____9904 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____9898 uu____9904)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____9911 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____9911) with
| true -> begin
(

let uu____9916 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____9916))
end
| uu____9920 -> begin
()
end));
(

let uu____9922 = (decorate e t2)
in ((uu____9922), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> ((

let uu____9950 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____9950) with
| true -> begin
(

let uu____9953 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "check_top_level, lc = %s\n" uu____9953))
end
| uu____9956 -> begin
()
end));
(

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____9967 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____9967) with
| true -> begin
(

let uu____9975 = (discharge g1)
in (

let uu____9977 = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((uu____9975), (uu____9977))))
end
| uu____9979 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let steps = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]
in (

let c1 = (

let uu____9986 = (

let uu____9987 = (

let uu____9988 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____9988 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____9987 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____9986 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____9990 = (destruct_comp c1)
in (match (uu____9990) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____10008 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____10009 = (

let uu____10014 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____10015 = (

let uu____10016 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____10025 = (

let uu____10036 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____10036)::[])
in (uu____10016)::uu____10025))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10014 uu____10015)))
in (uu____10009 FStar_Pervasives_Native.None uu____10008)))
in ((

let uu____10072 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10072) with
| true -> begin
(

let uu____10077 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____10077))
end
| uu____10080 -> begin
()
end));
(

let g2 = (

let uu____10083 = (FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Env.conj_guard g1 uu____10083))
in (

let uu____10084 = (discharge g2)
in (

let uu____10086 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____10084), (uu____10086)))));
))
end))))))
end))));
))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___351_10120 -> (match (uu___351_10120) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____10130))::[] -> begin
(f fst1)
end
| uu____10155 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____10167 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____10167 (fun _0_5 -> FStar_TypeChecker_Common.NonTrivial (_0_5)))))
in (

let op_or_e = (fun e -> (

let uu____10178 = (

let uu____10179 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____10179))
in (FStar_All.pipe_right uu____10178 (fun _0_6 -> FStar_TypeChecker_Common.NonTrivial (_0_6)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _0_7 -> FStar_TypeChecker_Common.NonTrivial (_0_7))))
in (

let op_or_t = (fun t -> (

let uu____10198 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____10198 (fun _0_8 -> FStar_TypeChecker_Common.NonTrivial (_0_8)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _0_9 -> FStar_TypeChecker_Common.NonTrivial (_0_9))))
in (

let short_op_ite = (fun uu___352_10212 -> (match (uu___352_10212) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____10222))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____10249))::[] -> begin
(

let uu____10290 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____10290 (fun _0_10 -> FStar_TypeChecker_Common.NonTrivial (_0_10))))
end
| uu____10291 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____10303 = (

let uu____10311 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____10311)))
in (

let uu____10319 = (

let uu____10329 = (

let uu____10337 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____10337)))
in (

let uu____10345 = (

let uu____10355 = (

let uu____10363 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____10363)))
in (

let uu____10371 = (

let uu____10381 = (

let uu____10389 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____10389)))
in (

let uu____10397 = (

let uu____10407 = (

let uu____10415 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____10415)))
in (uu____10407)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____10381)::uu____10397))
in (uu____10355)::uu____10371))
in (uu____10329)::uu____10345))
in (uu____10303)::uu____10319))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10477 = (FStar_Util.find_map table (fun uu____10492 -> (match (uu____10492) with
| (x, mk1) -> begin
(

let uu____10509 = (FStar_Ident.lid_equals x lid)
in (match (uu____10509) with
| true -> begin
(

let uu____10514 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____10514))
end
| uu____10515 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (uu____10477) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____10518 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____10526 = (

let uu____10527 = (FStar_Syntax_Util.un_uinst l)
in uu____10527.FStar_Syntax_Syntax.n)
in (match (uu____10526) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____10532 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____10568))::uu____10569 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____10588 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____10597, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10598))))::uu____10599 -> begin
bs
end
| uu____10617 -> begin
(

let uu____10618 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____10618) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____10622 = (

let uu____10623 = (FStar_Syntax_Subst.compress t)
in uu____10623.FStar_Syntax_Syntax.n)
in (match (uu____10622) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____10627) -> begin
(

let uu____10648 = (FStar_Util.prefix_until (fun uu___353_10688 -> (match (uu___353_10688) with
| (uu____10696, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10697))) -> begin
false
end
| uu____10702 -> begin
true
end)) bs')
in (match (uu____10648) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____10738, uu____10739) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____10811, uu____10812) -> begin
(

let uu____10885 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____10905 -> (match (uu____10905) with
| (x, uu____10914) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____10885) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____10963 -> (match (uu____10963) with
| (x, i) -> begin
(

let uu____10982 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____10982), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____10991 -> begin
bs
end))
end))
end
| uu____10993 -> begin
bs
end))
end))
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 t -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in (

let uu____11022 = (((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1)))
in (match (uu____11022) with
| true -> begin
e
end
| uu____11025 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end)))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____11053 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____11053) with
| true -> begin
e
end
| uu____11056 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____11096 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____11096) with
| true -> begin
((

let uu____11101 = (FStar_Ident.text_of_lid lident)
in (d uu____11101));
(

let uu____11103 = (FStar_Ident.text_of_lid lident)
in (

let uu____11105 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" uu____11103 uu____11105)));
)
end
| uu____11108 -> begin
()
end));
(

let fv = (

let uu____11111 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____11111 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (((FStar_Syntax_Util.mk_letbinding lbname [] FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def [] FStar_Range.dummyRange))::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____11123 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___374_11125 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___374_11125.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___374_11125.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___374_11125.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___374_11125.FStar_Syntax_Syntax.sigattrs})), (uu____11123)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (

let visibility = (fun uu___354_11143 -> (match (uu___354_11143) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11146 -> begin
false
end))
in (

let reducibility = (fun uu___355_11154 -> (match (uu___355_11154) with
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
| uu____11161 -> begin
false
end))
in (

let assumption = (fun uu___356_11169 -> (match (uu___356_11169) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____11173 -> begin
false
end))
in (

let reification = (fun uu___357_11181 -> (match (uu___357_11181) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____11184) -> begin
true
end
| uu____11186 -> begin
false
end))
in (

let inferred = (fun uu___358_11194 -> (match (uu___358_11194) with
| FStar_Syntax_Syntax.Discriminator (uu____11196) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____11198) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____11204) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____11214) -> begin
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
| uu____11227 -> begin
false
end))
in (

let has_eq = (fun uu___359_11235 -> (match (uu___359_11235) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____11239 -> begin
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
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((((Prims.op_Equality x q) || (Prims.op_Equality x FStar_Syntax_Syntax.Logic)) || (visibility x)) || (reducibility x)) || (reification x)) || (inferred x)) || (has_eq x)) || (env.FStar_TypeChecker_Env.is_iface && (Prims.op_Equality x FStar_Syntax_Syntax.Assumption))) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)))))
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
| FStar_Syntax_Syntax.Reflectable (uu____11318) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11325 -> begin
true
end))
in (

let quals = (FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se) (FStar_List.filter (fun x -> (not ((Prims.op_Equality x FStar_Syntax_Syntax.Logic))))))
in (

let uu____11336 = (

let uu____11338 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___360_11344 -> (match (uu___360_11344) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____11347 -> begin
false
end))))
in (FStar_All.pipe_right uu____11338 Prims.op_Negation))
in (match (uu____11336) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____11368 = (

let uu____11374 = (

let uu____11376 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____11376 msg))
in ((FStar_Errors.Fatal_QulifierListNotPermitted), (uu____11374)))
in (FStar_Errors.raise_error uu____11368 r)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err'1 = (fun uu____11394 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____11399 -> begin
()
end);
(

let uu____11402 = (

let uu____11404 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____11404)))
in (match (uu____11402) with
| true -> begin
(err "ill-formed combination")
end
| uu____11411 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____11414), uu____11415) -> begin
((

let uu____11427 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____11427) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____11434 -> begin
()
end));
(

let uu____11436 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____11436) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____11445 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____11447) -> begin
(

let uu____11456 = (

let uu____11458 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____11458)))
in (match (uu____11456) with
| true -> begin
(err'1 ())
end
| uu____11466 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____11468) -> begin
(

let uu____11475 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____11475) with
| true -> begin
(err'1 ())
end
| uu____11481 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____11483) -> begin
(

let uu____11490 = (

let uu____11492 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____11492)))
in (match (uu____11490) with
| true -> begin
(err'1 ())
end
| uu____11500 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____11502) -> begin
(

let uu____11503 = (

let uu____11505 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11505)))
in (match (uu____11503) with
| true -> begin
(err'1 ())
end
| uu____11513 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____11515) -> begin
(

let uu____11516 = (

let uu____11518 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11518)))
in (match (uu____11516) with
| true -> begin
(err'1 ())
end
| uu____11526 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____11528) -> begin
(

let uu____11541 = (

let uu____11543 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____11543)))
in (match (uu____11541) with
| true -> begin
(err'1 ())
end
| uu____11551 -> begin
()
end))
end
| uu____11553 -> begin
()
end);
))))))
end
| uu____11554 -> begin
()
end)))))))))))


let must_erase_for_extraction : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun g t -> (

let has_erased_for_extraction_attr = (fun fv -> (

let uu____11576 = (

let uu____11581 = (FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv)
in (FStar_All.pipe_right uu____11581 (FStar_TypeChecker_Env.lookup_attrs_of_lid g)))
in (FStar_All.pipe_right uu____11576 (fun l_opt -> ((FStar_Util.is_some l_opt) && (

let uu____11600 = (FStar_All.pipe_right l_opt FStar_Util.must)
in (FStar_All.pipe_right uu____11600 (FStar_List.existsb (fun t1 -> (

let uu____11618 = (

let uu____11619 = (FStar_Syntax_Subst.compress t1)
in uu____11619.FStar_Syntax_Syntax.n)
in (match (uu____11618) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_Ident.lid_equals fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.must_erase_for_extraction_attr) -> begin
true
end
| uu____11625 -> begin
false
end)))))))))))
in (

let rec aux_whnf = (fun env t1 -> (

let uu____11651 = (

let uu____11652 = (FStar_Syntax_Subst.compress t1)
in uu____11652.FStar_Syntax_Syntax.n)
in (match (uu____11651) with
| FStar_Syntax_Syntax.Tm_type (uu____11656) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (has_erased_for_extraction_attr fv))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____11659) -> begin
(

let uu____11674 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____11674) with
| (bs, c) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____11707 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____11707) with
| true -> begin
(aux env1 (FStar_Syntax_Util.comp_result c))
end
| uu____11711 -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____11713; FStar_Syntax_Syntax.index = uu____11714; FStar_Syntax_Syntax.sort = t2}, uu____11716) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____11725, uu____11726) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____11768)::[]) -> begin
(

let uu____11807 = (

let uu____11808 = (FStar_Syntax_Util.un_uinst head1)
in uu____11808.FStar_Syntax_Syntax.n)
in (match (uu____11807) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid) || (has_erased_for_extraction_attr fv))
end
| uu____11813 -> begin
false
end))
end
| uu____11815 -> begin
false
end)))
and aux = (fun env t1 -> (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::[]) env t1)
in (

let res = (aux_whnf env t2)
in ((

let uu____11825 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Extraction")))
in (match (uu____11825) with
| true -> begin
(

let uu____11830 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "must_erase=%s: %s\n" (match (res) with
| true -> begin
"true"
end
| uu____11836 -> begin
"false"
end) uu____11830))
end
| uu____11839 -> begin
()
end));
res;
))))
in (aux g t))))




