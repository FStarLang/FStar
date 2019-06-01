
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  unit = (fun env errs -> (

let uu____22 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____23 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.log_issue uu____22 uu____23))))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (FStar_TypeChecker_Env.new_implicit_var_aux reason r env k FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None))


let close_guard_implicits : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env xs g -> (

let uu____84 = (

let uu____86 = (FStar_Options.eager_subtyping ())
in (FStar_All.pipe_left Prims.op_Negation uu____86))
in (match (uu____84) with
| true -> begin
g
end
| uu____91 -> begin
(

let uu____93 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred (FStar_List.partition (fun uu____145 -> (match (uu____145) with
| (uu____152, p) -> begin
(FStar_TypeChecker_Rel.flex_prob_closing env xs p)
end))))
in (match (uu____93) with
| (solve_now, defer) -> begin
((

let uu____187 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____187) with
| true -> begin
((FStar_Util.print_string "SOLVE BEFORE CLOSING:\n");
(FStar_List.iter (fun uu____204 -> (match (uu____204) with
| (s, p) -> begin
(

let uu____214 = (FStar_TypeChecker_Rel.prob_to_string env p)
in (FStar_Util.print2 "%s: %s\n" s uu____214))
end)) solve_now);
(FStar_Util.print_string " ...DEFERRED THE REST:\n");
(FStar_List.iter (fun uu____229 -> (match (uu____229) with
| (s, p) -> begin
(

let uu____239 = (FStar_TypeChecker_Rel.prob_to_string env p)
in (FStar_Util.print2 "%s: %s\n" s uu____239))
end)) defer);
(FStar_Util.print_string "END\n");
)
end
| uu____243 -> begin
()
end));
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env (

let uu___46_247 = g
in {FStar_TypeChecker_Env.guard_f = uu___46_247.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = solve_now; FStar_TypeChecker_Env.univ_ineqs = uu___46_247.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___46_247.FStar_TypeChecker_Env.implicits}))
in (

let g2 = (

let uu___49_249 = g1
in {FStar_TypeChecker_Env.guard_f = uu___49_249.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = defer; FStar_TypeChecker_Env.univ_ineqs = uu___49_249.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___49_249.FStar_TypeChecker_Env.implicits})
in g2));
)
end))
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____264 = (

let uu____266 = (FStar_Util.set_is_empty uvs)
in (not (uu____266)))
in (match (uu____264) with
| true -> begin
(

let us = (

let uu____271 = (

let uu____275 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun u -> (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)) uu____275))
in (FStar_All.pipe_right uu____271 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____294 = (

let uu____300 = (

let uu____302 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____302))
in ((FStar_Errors.Error_UncontrainedUnificationVar), (uu____300)))
in (FStar_Errors.log_issue r uu____294));
(FStar_Options.pop ());
))
end
| uu____306 -> begin
()
end))))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____325 -> (match (uu____325) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____336; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____338; FStar_Syntax_Syntax.lbpos = uu____339} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____374 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 e)
in (match (uu____374) with
| (univ_vars2, e1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars2)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let rec aux = (fun e2 -> (

let e3 = (FStar_Syntax_Subst.compress e2)
in (match (e3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e4, uu____412) -> begin
(aux e4)
end
| FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____419) -> begin
(FStar_Pervasives_Native.fst t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____474) -> begin
(

let res = (aux body)
in (

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____510 = (FStar_Options.ml_ish ())
in (match (uu____510) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____515 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in ((

let uu____532 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____532) with
| true -> begin
(

let uu____535 = (FStar_Range.string_of_range r)
in (

let uu____537 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Using type %s\n" uu____535 uu____537)))
end
| uu____540 -> begin
()
end));
FStar_Util.Inl (t2);
))))
end
| uu____542 -> begin
FStar_Util.Inl (FStar_Syntax_Syntax.tun)
end)))
in (

let t2 = (

let uu____544 = (aux e1)
in (match (uu____544) with
| FStar_Util.Inr (c) -> begin
(

let uu____550 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____550) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____553 -> begin
(

let uu____555 = (

let uu____561 = (

let uu____563 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____563))
in ((FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec), (uu____561)))
in (FStar_Errors.raise_error uu____555 rng))
end))
end
| FStar_Util.Inl (t2) -> begin
t2
end))
in ((univ_vars2), (t2), (true))))))
end))
end
| uu____572 -> begin
(

let uu____573 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____573) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____637 -> (match (uu____637) with
| (p, i) -> begin
(

let uu____657 = (decorated_pattern_as_term p)
in (match (uu____657) with
| (vars, te) -> begin
(

let uu____680 = (

let uu____685 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____685)))
in ((vars), (uu____680)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____699 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____699)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____703 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____703)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____707 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____707)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____730 = (

let uu____749 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____749 FStar_List.unzip))
in (match (uu____730) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____887 = (

let uu____888 = (

let uu____889 = (

let uu____906 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____906), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____889))
in (mk1 uu____888))
in ((vars1), (uu____887))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let comp_univ_opt : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____945, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.GTotal (uu____955, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::uu____969 -> begin
FStar_Pervasives_Native.Some (hd1)
end)
end))


let lcomp_univ_opt : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun lc -> (

let uu____980 = (FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp)
in (FStar_All.pipe_right uu____980 comp_univ_opt)))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____1009))::[] -> begin
wp
end
| uu____1034 -> begin
(

let uu____1045 = (

let uu____1047 = (

let uu____1049 = (FStar_List.map (fun uu____1063 -> (match (uu____1063) with
| (x, uu____1072) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right uu____1049 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____1047))
in (failwith uu____1045))
end)
in (

let uu____1083 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____1083), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  FStar_TypeChecker_Env.mlift  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let uu____1100 = (destruct_comp c)
in (match (uu____1100) with
| (u, uu____1108, wp) -> begin
(

let uu____1110 = (

let uu____1121 = (

let uu____1130 = (lift.FStar_TypeChecker_Env.mlift_wp u c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____1130))
in (uu____1121)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____1110; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____1163 = (

let uu____1170 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____1171 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____1170 uu____1171)))
in (match (uu____1163) with
| (m, uu____1173, uu____1174) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____1191 = ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2))
in (match (uu____1191) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____1194 -> begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)))


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____1238 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____1238) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c11 m lift1)
in (

let m2 = (lift_comp c21 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____1275 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (uu____1275) with
| (a, kwp) -> begin
(

let uu____1306 = (destruct_comp m1)
in (

let uu____1313 = (destruct_comp m2)
in ((((md), (a), (kwp))), (uu____1306), (uu____1313))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (

let uu____1398 = (

let uu____1399 = (

let uu____1410 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1410)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____1399; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp uu____1398)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (

let uu____1494 = (FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)
in (match (uu____1494) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____1497 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst1 lc -> (

let uu____1510 = (FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____1510 lc.FStar_Syntax_Syntax.cflags (fun uu____1513 -> (

let uu____1514 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Subst.subst_comp subst1 uu____1514))))))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1522 = (

let uu____1523 = (FStar_Syntax_Subst.compress t)
in uu____1523.FStar_Syntax_Syntax.n)
in (match (uu____1522) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1527) -> begin
true
end
| uu____1543 -> begin
false
end)))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (reason1) -> begin
(

let uu____1613 = (

let uu____1615 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____1615))
in (match (uu____1613) with
| true -> begin
f
end
| uu____1620 -> begin
(

let uu____1622 = (reason1 ())
in (label uu____1622 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___243_1643 = g
in (

let uu____1644 = (

let uu____1645 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____1645))
in {FStar_TypeChecker_Env.guard_f = uu____1644; FStar_TypeChecker_Env.deferred = uu___243_1643.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___243_1643.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___243_1643.FStar_TypeChecker_Env.implicits}))
end))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____1666 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____1666) with
| true -> begin
c
end
| uu____1669 -> begin
(

let uu____1671 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____1671) with
| true -> begin
c
end
| uu____1674 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____1733 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1733)::[])
in (

let us = (

let uu____1755 = (

let uu____1758 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____1758)::[])
in (u_res)::uu____1755)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____1764 = (

let uu____1769 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (

let uu____1770 = (

let uu____1771 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____1780 = (

let uu____1791 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____1800 = (

let uu____1811 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____1811)::[])
in (uu____1791)::uu____1800))
in (uu____1771)::uu____1780))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1769 uu____1770)))
in (uu____1764 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____1853 = (destruct_comp c1)
in (match (uu____1853) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end)))


let close_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____1889 -> (

let uu____1890 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (close_comp env bvs uu____1890)))))


let close_comp_if_refinement_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env t x c -> (

let t1 = (FStar_TypeChecker_Normalize.normalize_refinement FStar_TypeChecker_Normalize.whnf_steps env t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____1913; FStar_Syntax_Syntax.index = uu____1914; FStar_Syntax_Syntax.sort = {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____1916; FStar_Syntax_Syntax.vars = uu____1917}}, uu____1918) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(close_comp env ((x)::[]) c)
end
| uu____1926 -> begin
c
end)))


let should_not_inline_lc : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___0_1938 -> (match (uu___0_1938) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____1941 -> begin
false
end)))))


let should_return : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun env eopt lc -> (

let lc_is_unit_or_effectful = (

let uu____1966 = (

let uu____1969 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ FStar_Syntax_Util.arrow_formals_comp)
in (FStar_All.pipe_right uu____1969 FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____1966 (fun c -> ((

let uu____2025 = (FStar_TypeChecker_Env.is_reifiable_comp env c)
in (not (uu____2025))) && ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Util.is_unit) || (

let uu____2029 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____2029))))))))
in (match (eopt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (e) -> begin
((((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) && (not (lc_is_unit_or_effectful))) && (

let uu____2040 = (FStar_Syntax_Util.head_and_args' e)
in (match (uu____2040) with
| (head1, uu____2057) -> begin
(

let uu____2078 = (

let uu____2079 = (FStar_Syntax_Util.un_uinst head1)
in uu____2079.FStar_Syntax_Syntax.n)
in (match (uu____2078) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2084 = (

let uu____2086 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_irreducible env uu____2086))
in (not (uu____2084)))
end
| uu____2087 -> begin
true
end))
end))) && (

let uu____2090 = (should_not_inline_lc lc)
in (not (uu____2090))))
end)))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env u_t_opt t v1 -> (

let c = (

let uu____2118 = (

let uu____2120 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____2120))
in (match (uu____2118) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____2125 -> begin
(

let uu____2127 = (FStar_Syntax_Util.is_unit t)
in (match (uu____2127) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero)))
end
| uu____2130 -> begin
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

let uu____2136 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2136) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____2139 -> begin
(

let uu____2141 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____2141) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let uu____2151 = (

let uu____2152 = (

let uu____2157 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2158 = (

let uu____2159 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____2168 = (

let uu____2179 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____2179)::[])
in (uu____2159)::uu____2168))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2157 uu____2158)))
in (uu____2152 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::[]) env uu____2151)))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
end))
in ((

let uu____2213 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____2213) with
| true -> begin
(

let uu____2218 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____2220 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____2222 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2218 uu____2220 uu____2222))))
end
| uu____2225 -> begin
()
end));
c;
)))


let weaken_flags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags -> (

let uu____2239 = (FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___1_2245 -> (match (uu___1_2245) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____2248 -> begin
false
end))))
in (match (uu____2239) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____2253 -> begin
(FStar_All.pipe_right flags (FStar_List.collect (fun uu___2_2260 -> (match (uu___2_2260) with
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

let uu____2280 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____2280) with
| true -> begin
c
end
| uu____2283 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____2286 = (destruct_comp c1)
in (match (uu____2286) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____2300 = (

let uu____2305 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (

let uu____2306 = (

let uu____2307 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____2316 = (

let uu____2327 = (FStar_Syntax_Syntax.as_arg formula)
in (

let uu____2336 = (

let uu____2347 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2347)::[])
in (uu____2327)::uu____2336))
in (uu____2307)::uu____2316))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2305 uu____2306)))
in (uu____2300 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (

let uu____2388 = (weaken_flags c1.FStar_Syntax_Syntax.flags)
in (mk_comp md u_res_t res_t wp1 uu____2388))))
end)))
end)))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun uu____2412 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let uu____2414 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2414) with
| true -> begin
c
end
| uu____2417 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(weaken_comp env c f1)
end)
end))))
in (

let uu____2420 = (weaken_flags lc.FStar_Syntax_Syntax.cflags)
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ uu____2420 weaken))))


let strengthen_comp : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun env reason c f flags -> (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____2465 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____2468 = (destruct_comp c1)
in (match (uu____2468) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (

let uu____2482 = (

let uu____2487 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (

let uu____2488 = (

let uu____2489 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____2498 = (

let uu____2509 = (

let uu____2518 = (

let uu____2519 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason uu____2519 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2518))
in (

let uu____2528 = (

let uu____2539 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2539)::[])
in (uu____2509)::uu____2528))
in (uu____2489)::uu____2498))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2487 uu____2488)))
in (uu____2482 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 flags)))
end)))
end))


let strengthen_precondition : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e_for_debugging_only lc g0 -> (

let uu____2625 = (FStar_TypeChecker_Env.is_trivial_guard_formula g0)
in (match (uu____2625) with
| true -> begin
((lc), (g0))
end
| uu____2632 -> begin
(

let flags = (

let uu____2637 = (

let uu____2645 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____2645) with
| true -> begin
((true), ((FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]))
end
| uu____2659 -> begin
((false), ([]))
end))
in (match (uu____2637) with
| (maybe_trivial_post, flags) -> begin
(

let uu____2675 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___3_2683 -> (match (uu___3_2683) with
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
| uu____2686 -> begin
[]
end))))
in (FStar_List.append flags uu____2675))
end))
in (

let strengthen = (fun uu____2692 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
c
end
| uu____2695 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____2698 = (FStar_TypeChecker_Env.guard_form g01)
in (match (uu____2698) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____2701 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____2701) with
| true -> begin
(

let uu____2705 = (FStar_TypeChecker_Normalize.term_to_string env e_for_debugging_only)
in (

let uu____2707 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____2705 uu____2707)))
end
| uu____2710 -> begin
()
end));
(strengthen_comp env reason c f flags);
)
end)))
end)))
in (

let uu____2712 = (

let uu____2713 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____2713 lc.FStar_Syntax_Syntax.res_typ flags strengthen))
in ((uu____2712), ((

let uu___398_2715 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___398_2715.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___398_2715.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___398_2715.FStar_TypeChecker_Env.implicits}))))))
end)))


let lcomp_has_trivial_postcondition : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) || (FStar_Util.for_some (fun uu___4_2724 -> (match (uu___4_2724) with
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
true
end
| uu____2728 -> begin
false
end)) lc.FStar_Syntax_Syntax.cflags)))


let maybe_add_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env uopt lc e -> (

let uu____2757 = ((FStar_Syntax_Util.is_lcomp_partial_return lc) || env.FStar_TypeChecker_Env.lax)
in (match (uu____2757) with
| true -> begin
e
end
| uu____2762 -> begin
(

let uu____2764 = ((lcomp_has_trivial_postcondition lc) && (

let uu____2767 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____2767)))
in (match (uu____2764) with
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
| uu____2791 -> begin
e
end))
end)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 uu____2820 -> (match (uu____2820) with
| (b, lc2) -> begin
(

let debug1 = (fun f -> (

let uu____2840 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____2840) with
| true -> begin
(f ())
end
| uu____2845 -> begin
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

let uu____2853 = ((should_not_inline_lc lc11) || (should_not_inline_lc lc21))
in (match (uu____2853) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____2858 -> begin
(

let flags = (

let uu____2863 = (FStar_Syntax_Util.is_total_lcomp lc11)
in (match (uu____2863) with
| true -> begin
(

let uu____2868 = (FStar_Syntax_Util.is_total_lcomp lc21)
in (match (uu____2868) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____2873 -> begin
(

let uu____2875 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
in (match (uu____2875) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____2880 -> begin
[]
end))
end))
end
| uu____2882 -> begin
(

let uu____2884 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) && (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21))
in (match (uu____2884) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____2889 -> begin
[]
end))
end))
in (

let uu____2891 = (lcomp_has_trivial_postcondition lc21)
in (match (uu____2891) with
| true -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::flags
end
| uu____2896 -> begin
flags
end)))
end))
in (

let bind_it = (fun uu____2903 -> (

let uu____2904 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2904) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_Syntax_Syntax.res_typ []))
end
| uu____2908 -> begin
(

let c1 = (FStar_Syntax_Syntax.lcomp_comp lc11)
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp lc21)
in ((debug1 (fun uu____2921 -> (

let uu____2922 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____2924 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____2929 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n" uu____2922 uu____2924 uu____2929))))));
(

let aux = (fun uu____2947 -> (

let uu____2948 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____2948) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____2979) -> begin
(

let uu____2980 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____2980) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____3001 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____3010 -> begin
(

let uu____3012 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____3012) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____3033 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let try_simplify = (fun uu____3057 -> (

let uu____3058 = (

let uu____3060 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____3060))
in (match (uu____3058) with
| true -> begin
(

let uu____3074 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3074) with
| true -> begin
FStar_Util.Inl (((c2), ("Early in prims; we don\'t have bind yet")))
end
| uu____3095 -> begin
(

let uu____3097 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonTrivialPreConditionInPrims), ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")) uu____3097))
end))
end
| uu____3110 -> begin
(

let uu____3112 = (FStar_Syntax_Util.is_total_comp c1)
in (match (uu____3112) with
| true -> begin
(

let close1 = (fun x reason c -> (

let x1 = (

let uu___464_3154 = x
in {FStar_Syntax_Syntax.ppname = uu___464_3154.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___464_3154.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____3155 = (

let uu____3161 = (close_comp_if_refinement_t env x1.FStar_Syntax_Syntax.sort x1 c)
in ((uu____3161), (reason)))
in FStar_Util.Inl (uu____3155))))
in (match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____3197 = (FStar_All.pipe_right c2 (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[])))
in (FStar_All.pipe_right uu____3197 (close1 x "c1 Tot")))
end
| (uu____3211, FStar_Pervasives_Native.Some (x)) -> begin
(FStar_All.pipe_right c2 (close1 x "c1 Tot only close"))
end
| (uu____3234, uu____3235) -> begin
(aux ())
end))
end
| uu____3248 -> begin
(

let uu____3250 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____3250) with
| true -> begin
(

let uu____3263 = (

let uu____3269 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____3269), ("both GTot")))
in FStar_Util.Inl (uu____3263))
end
| uu____3278 -> begin
(aux ())
end))
end))
end)))
in (

let uu____3280 = (try_simplify ())
in (match (uu____3280) with
| FStar_Util.Inl (c, reason) -> begin
((debug1 (fun uu____3306 -> (

let uu____3307 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "(2) bind: Simplified (because %s) to\n\t%s\n" reason uu____3307))));
c;
)
end
| FStar_Util.Inr (reason) -> begin
((debug1 (fun uu____3321 -> (FStar_Util.print1 "(2) bind: Not simplified because %s\n" reason)));
(

let mk_bind = (fun c11 b1 c21 -> (

let uu____3343 = (lift_and_destruct env c11 c21)
in (match (uu____3343) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b1) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3396 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____3396)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____3416 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3416)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____3463 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____3472 = (

let uu____3483 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3492 = (

let uu____3503 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____3512 = (

let uu____3523 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____3532 = (

let uu____3543 = (

let uu____3552 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____3552))
in (uu____3543)::[])
in (uu____3523)::uu____3532))
in (uu____3503)::uu____3512))
in (uu____3483)::uu____3492))
in (uu____3463)::uu____3472))
in (

let wp = (

let uu____3604 = (

let uu____3609 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3609 wp_args))
in (uu____3604 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (mk_comp md u_t2 t2 wp bind_flags))))))
end)))
in (

let mk_seq = (fun c11 b1 c21 -> (

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in (

let uu____3632 = (FStar_TypeChecker_Env.join env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____3632) with
| (m, uu____3640, lift2) -> begin
(

let c23 = (

let uu____3643 = (lift_comp c22 m lift2)
in (FStar_Syntax_Syntax.mk_Comp uu____3643))
in (

let uu____3644 = (destruct_comp c12)
in (match (uu____3644) with
| (u1, t1, wp1) -> begin
(

let md_pure_or_ghost = (FStar_TypeChecker_Env.get_effect_decl env c12.FStar_Syntax_Syntax.effect_name)
in (

let vc1 = (

let uu____3658 = (

let uu____3663 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u1)::[]) env md_pure_or_ghost md_pure_or_ghost.FStar_Syntax_Syntax.trivial)
in (

let uu____3664 = (

let uu____3665 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3674 = (

let uu____3685 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____3685)::[])
in (uu____3665)::uu____3674))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3663 uu____3664)))
in (uu____3658 FStar_Pervasives_Native.None r1))
in (strengthen_comp env FStar_Pervasives_Native.None c23 vc1 bind_flags)))
end)))
end)))))
in (

let c1_typ = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let uu____3723 = (destruct_comp c1_typ)
in (match (uu____3723) with
| (u_res_t1, res_t1, uu____3732) -> begin
(

let uu____3733 = ((FStar_Option.isSome b) && (should_return env e1opt lc11))
in (match (uu____3733) with
| true -> begin
(

let e1 = (FStar_Option.get e1opt)
in (

let x = (FStar_Option.get b)
in (

let uu____3738 = (FStar_Syntax_Util.is_partial_return c1)
in (match (uu____3738) with
| true -> begin
((debug1 (fun uu____3748 -> (

let uu____3749 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____3751 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case a): Substituting %s for %s" uu____3749 uu____3751)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (mk_bind c1 b c21));
)
end
| uu____3757 -> begin
(

let uu____3759 = (((FStar_Options.vcgen_optimize_bind_as_seq ()) && (lcomp_has_trivial_postcondition lc11)) && (

let uu____3762 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____3762)))
in (match (uu____3759) with
| true -> begin
(

let e1' = (

let uu____3783 = (FStar_Options.vcgen_decorate_with_type ())
in (match (uu____3783) with
| true -> begin
(FStar_Syntax_Util.mk_with_type u_res_t1 res_t1 e1)
end
| uu____3786 -> begin
e1
end))
in ((debug1 (fun uu____3795 -> (

let uu____3796 = (FStar_TypeChecker_Normalize.term_to_string env e1')
in (

let uu____3798 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case b): Substituting %s for %s" uu____3796 uu____3798)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1'))))::[]) c2)
in (mk_seq c1 b c21));
))
end
| uu____3804 -> begin
((debug1 (fun uu____3813 -> (

let uu____3814 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____3816 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case c): Adding equality %s = %s" uu____3814 uu____3816)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (

let x_eq_e = (

let uu____3823 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq2 u_res_t1 res_t1 e1 uu____3823))
in (

let c22 = (weaken_comp env c21 x_eq_e)
in (mk_bind c1 b c22))));
)
end))
end))))
end
| uu____3825 -> begin
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
| uu____3841 -> begin
g2
end))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let should_return1 = ((((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)) && (should_return env (FStar_Pervasives_Native.Some (e)) lc)) && (

let uu____3865 = (FStar_Syntax_Util.is_lcomp_partial_return lc)
in (not (uu____3865))))
in (

let flags = (match (should_return1) with
| true -> begin
(

let uu____3873 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____3873) with
| true -> begin
(FStar_Syntax_Syntax.RETURN)::lc.FStar_Syntax_Syntax.cflags
end
| uu____3878 -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end))
end
| uu____3880 -> begin
lc.FStar_Syntax_Syntax.cflags
end)
in (

let refine1 = (fun uu____3889 -> (

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

let uu____3893 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____3893) with
| true -> begin
(

let retc = (return_value env (FStar_Pervasives_Native.Some (u_t)) (FStar_Syntax_Util.comp_result c) e)
in (

let uu____3899 = (

let uu____3901 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____3901)))
in (match (uu____3899) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___583_3908 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___583_3908.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___583_3908.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___583_3908.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp retc2)))
end
| uu____3909 -> begin
(FStar_Syntax_Util.comp_set_flags retc flags)
end)))
end
| uu____3911 -> begin
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

let uu____3921 = (

let uu____3922 = (return_value env (FStar_Pervasives_Native.Some (u_t)) t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____3922 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3921))
in (

let eq1 = (FStar_Syntax_Util.mk_eq2 u_t t xexp e)
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____3925 = (

let uu____3926 = (

let uu____3927 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None uu____3927 ((FStar_Pervasives_Native.Some (x)), (eq_ret))))
in (FStar_Syntax_Syntax.lcomp_comp uu____3926))
in (FStar_Syntax_Util.comp_set_flags uu____3925 flags))))))))))
end)))))
in (match ((not (should_return1))) with
| true -> begin
lc
end
| uu____3931 -> begin
(FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ flags refine1)
end)))))


let maybe_return_e2_and_bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r env e1opt lc1 e2 uu____3965 -> (match (uu____3965) with
| (x, lc2) -> begin
(

let lc21 = (

let eff1 = (FStar_TypeChecker_Env.norm_eff_name env lc1.FStar_Syntax_Syntax.eff_name)
in (

let eff2 = (FStar_TypeChecker_Env.norm_eff_name env lc2.FStar_Syntax_Syntax.eff_name)
in (

let uu____3977 = (((

let uu____3981 = (is_pure_or_ghost_effect env eff1)
in (not (uu____3981))) || (should_not_inline_lc lc1)) && (is_pure_or_ghost_effect env eff2))
in (match (uu____3977) with
| true -> begin
(maybe_assume_result_eq_pure_term env e2 lc2)
end
| uu____3984 -> begin
lc2
end))))
in (bind r env e1opt lc1 ((x), (lc21))))
end))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____3999 = (

let uu____4000 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____4000))
in (FStar_Syntax_Syntax.fvar uu____3999 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp)) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____4070 -> (match (uu____4070) with
| (uu____4084, eff_label, uu____4086, uu____4087) -> begin
(join_effects env eff eff_label)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let uu____4100 = (

let uu____4108 = (FStar_All.pipe_right lcases (FStar_Util.for_some (fun uu____4146 -> (match (uu____4146) with
| (uu____4161, uu____4162, flags, uu____4164) -> begin
(FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___5_4181 -> (match (uu___5_4181) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____4184 -> begin
false
end))))
end))))
in (match (uu____4108) with
| true -> begin
((true), ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
end
| uu____4198 -> begin
((false), ([]))
end))
in (match (uu____4100) with
| (should_not_inline_whole_match, bind_cases_flags) -> begin
(

let bind_cases = (fun uu____4217 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____4219 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4219) with
| true -> begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end
| uu____4222 -> begin
(

let ifthenelse = (fun md res_t1 g wp_t wp_e -> (

let uu____4260 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____4261 = (

let uu____4266 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (

let uu____4267 = (

let uu____4268 = (FStar_Syntax_Syntax.as_arg res_t1)
in (

let uu____4277 = (

let uu____4288 = (FStar_Syntax_Syntax.as_arg g)
in (

let uu____4297 = (

let uu____4308 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____4317 = (

let uu____4328 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____4328)::[])
in (uu____4308)::uu____4317))
in (uu____4288)::uu____4297))
in (uu____4268)::uu____4277))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4266 uu____4267)))
in (uu____4261 FStar_Pervasives_Native.None uu____4260))))
in (

let default_case = (

let post_k = (

let uu____4381 = (

let uu____4390 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____4390)::[])
in (

let uu____4409 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____4381 uu____4409)))
in (

let kwp = (

let uu____4415 = (

let uu____4424 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____4424)::[])
in (

let uu____4443 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____4415 uu____4443)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____4450 = (

let uu____4451 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____4451)::[])
in (

let uu____4470 = (

let uu____4473 = (

let uu____4480 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____4480))
in (

let uu____4481 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____4473 uu____4481)))
in (FStar_Syntax_Util.abs uu____4450 uu____4470 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let maybe_return = (fun eff_label_then cthen -> (

let uu____4505 = (should_not_inline_whole_match || (

let uu____4508 = (is_pure_or_ghost_effect env eff)
in (not (uu____4508))))
in (match (uu____4505) with
| true -> begin
(cthen true)
end
| uu____4512 -> begin
(cthen false)
end)))
in (

let comp = (FStar_List.fold_right (fun uu____4547 celse -> (match (uu____4547) with
| (g, eff_label, uu____4564, cthen) -> begin
(

let uu____4578 = (

let uu____4603 = (

let uu____4604 = (maybe_return eff_label cthen)
in (FStar_Syntax_Syntax.lcomp_comp uu____4604))
in (lift_and_destruct env uu____4603 celse))
in (match (uu____4578) with
| ((md, uu____4606, uu____4607), (uu____4608, uu____4609, wp_then), (uu____4611, uu____4612, wp_else)) -> begin
(

let uu____4632 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t uu____4632 []))
end))
end)) lcases default_case)
in (match (lcases) with
| [] -> begin
comp
end
| (uu____4647)::[] -> begin
comp
end
| uu____4690 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____4709 = (destruct_comp comp1)
in (match (uu____4709) with
| (uu____4716, uu____4717, wp) -> begin
(

let wp1 = (

let uu____4722 = (

let uu____4727 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (

let uu____4728 = (

let uu____4729 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____4738 = (

let uu____4749 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____4749)::[])
in (uu____4729)::uu____4738))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4727 uu____4728)))
in (uu____4722 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (mk_comp md u_res_t res_t wp1 bind_cases_flags))
end))))
end)))))
end))))
in (FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags bind_cases))
end))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (

let uu____4815 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____4815) with
| FStar_Pervasives_Native.None -> begin
(match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(

let uu____4831 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq env e c c')
in (

let uu____4837 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____4831 uu____4837)))
end
| uu____4844 -> begin
(

let uu____4846 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____4852 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____4846 uu____4852)))
end)
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let universe_of_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe = (fun env u_res c -> (

let c_lid = (

let uu____4877 = (FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name)
in (FStar_All.pipe_right uu____4877 (FStar_TypeChecker_Env.norm_eff_name env)))
in (

let uu____4880 = (FStar_Syntax_Util.is_pure_or_ghost_effect c_lid)
in (match (uu____4880) with
| true -> begin
u_res
end
| uu____4883 -> begin
(

let is_total = (

let uu____4887 = (FStar_TypeChecker_Env.lookup_effect_quals env c_lid)
in (FStar_All.pipe_right uu____4887 (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.TotalEffect)))))
in (match ((not (is_total))) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____4896 -> begin
(

let uu____4898 = (FStar_TypeChecker_Env.effect_repr env c u_res)
in (match (uu____4898) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4901 = (

let uu____4907 = (

let uu____4909 = (FStar_Syntax_Print.lid_to_string c_lid)
in (FStar_Util.format1 "Effect %s is marked total but does not have a repr" uu____4909))
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____4907)))
in (FStar_Errors.raise_error uu____4901 c.FStar_Syntax_Syntax.pos))
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
| uu____4944 -> begin
(

let is_type1 = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____4954 = (

let uu____4955 = (FStar_Syntax_Subst.compress t2)
in uu____4955.FStar_Syntax_Syntax.n)
in (match (uu____4954) with
| FStar_Syntax_Syntax.Tm_type (uu____4959) -> begin
true
end
| uu____4961 -> begin
false
end))))
in (

let uu____4963 = (

let uu____4964 = (FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ)
in uu____4964.FStar_Syntax_Syntax.n)
in (match (uu____4963) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 t)) -> begin
(

let uu____4972 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.b2t_lid)
in (

let b2t1 = (

let uu____4982 = (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____4982 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let lc1 = (

let uu____4985 = (

let uu____4986 = (

let uu____4987 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4987))
in ((FStar_Pervasives_Native.None), (uu____4986)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____4985))
in (

let e1 = (

let uu____4993 = (

let uu____4998 = (

let uu____4999 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4999)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4998))
in (uu____4993 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1))))))
end
| uu____5024 -> begin
((e), (lc))
end)))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> ((

let uu____5059 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5059) with
| true -> begin
(

let uu____5062 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5064 = (FStar_Syntax_Print.lcomp_to_string lc)
in (

let uu____5066 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n" uu____5062 uu____5064 uu____5066))))
end
| uu____5069 -> begin
()
end));
(

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____5076 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____5076) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____5101 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____5127 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5127), (false)))
end
| uu____5135 -> begin
(

let uu____5137 = (FStar_TypeChecker_Rel.get_subtyping_predicate env lc.FStar_Syntax_Syntax.res_typ t)
in ((uu____5137), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____5150) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____5162 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Errors.raise_error uu____5162 e.FStar_Syntax_Syntax.pos))
end
| uu____5174 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t);
((e), ((

let uu___739_5178 = lc
in {FStar_Syntax_Syntax.eff_name = uu___739_5178.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___739_5178.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___739_5178.FStar_Syntax_Syntax.comp_thunk})), (FStar_TypeChecker_Env.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____5185 = (FStar_TypeChecker_Env.guard_form g)
in (match (uu____5185) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let strengthen_trivial = (fun uu____5197 -> (

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let set_result_typ1 = (fun c1 -> (FStar_Syntax_Util.set_result_typ c1 t))
in (

let uu____5208 = (

let uu____5210 = (FStar_Syntax_Util.eq_tm t res_t)
in (Prims.op_Equality uu____5210 FStar_Syntax_Util.Equal))
in (match (uu____5208) with
| true -> begin
((

let uu____5213 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5213) with
| true -> begin
(

let uu____5217 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____5219 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n" uu____5217 uu____5219)))
end
| uu____5222 -> begin
()
end));
(set_result_typ1 c);
)
end
| uu____5224 -> begin
(

let is_res_t_refinement = (

let res_t1 = (FStar_TypeChecker_Normalize.normalize_refinement FStar_TypeChecker_Normalize.whnf_steps env res_t)
in (match (res_t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (uu____5230) -> begin
true
end
| uu____5238 -> begin
false
end))
in (match (is_res_t_refinement) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (res_t.FStar_Syntax_Syntax.pos)) res_t)
in (

let cret = (

let uu____5243 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env (comp_univ_opt c) res_t uu____5243))
in (

let lc1 = (

let uu____5245 = (FStar_Syntax_Util.lcomp_of_comp c)
in (

let uu____5246 = (

let uu____5247 = (FStar_Syntax_Util.lcomp_of_comp cret)
in ((FStar_Pervasives_Native.Some (x)), (uu____5247)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____5245 uu____5246)))
in ((

let uu____5251 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5251) with
| true -> begin
(

let uu____5255 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5257 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____5259 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____5261 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (FStar_Util.print4 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n" uu____5255 uu____5257 uu____5259 uu____5261)))))
end
| uu____5264 -> begin
()
end));
(

let uu____5266 = (FStar_Syntax_Syntax.lcomp_comp lc1)
in (set_result_typ1 uu____5266));
))))
end
| uu____5267 -> begin
((

let uu____5270 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5270) with
| true -> begin
(

let uu____5274 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____5276 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n" uu____5274 uu____5276)))
end
| uu____5279 -> begin
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

let uu___771_5284 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___771_5284.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___771_5284.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___771_5284.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun uu____5290 -> (

let uu____5291 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5291) with
| true -> begin
(FStar_Syntax_Syntax.lcomp_comp lc)
end
| uu____5294 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::[]) env f)
in (

let uu____5297 = (

let uu____5298 = (FStar_Syntax_Subst.compress f1)
in uu____5298.FStar_Syntax_Syntax.n)
in (match (uu____5297) with
| FStar_Syntax_Syntax.Tm_abs (uu____5301, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5303; FStar_Syntax_Syntax.vars = uu____5304}, uu____5305) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___787_5331 = lc
in {FStar_Syntax_Syntax.eff_name = uu___787_5331.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___787_5331.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___787_5331.FStar_Syntax_Syntax.comp_thunk})
in (FStar_Syntax_Syntax.lcomp_comp lc1))
end
| uu____5332 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((

let uu____5335 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5335) with
| true -> begin
(

let uu____5339 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____5341 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____5343 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____5345 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____5339 uu____5341 uu____5343 uu____5345)))))
end
| uu____5348 -> begin
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

let uu____5358 = (

let uu____5363 = (

let uu____5364 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____5364)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____5363))
in (uu____5358 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____5389 -> begin
f1
end)
in (

let uu____5391 = (

let uu____5396 = (FStar_All.pipe_left (fun _5417 -> FStar_Pervasives_Native.Some (_5417)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (

let uu____5418 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____5419 = (FStar_Syntax_Util.lcomp_of_comp cret)
in (

let uu____5420 = (FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____5396 uu____5418 e uu____5419 uu____5420)))))
in (match (uu____5391) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___803_5424 = x
in {FStar_Syntax_Syntax.ppname = uu___803_5424.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___803_5424.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c1 = (

let uu____5426 = (FStar_Syntax_Util.lcomp_of_comp c)
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____5426 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let c2 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((

let uu____5431 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____5431) with
| true -> begin
(

let uu____5435 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____5435))
end
| uu____5438 -> begin
()
end));
c2;
))))
end)))))));
))
end)))
end)))
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun uu___6_5448 -> (match (uu___6_5448) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____5451 -> begin
[]
end))))
in (

let lc1 = (

let uu____5453 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Syntax.mk_lcomp uu____5453 t flags strengthen))
in (

let g2 = (

let uu___817_5455 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___817_5455.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___817_5455.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___817_5455.FStar_TypeChecker_Env.implicits})
in ((e), (lc1), (g2)))))))
end))
end)));
))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____5491 = (

let uu____5494 = (

let uu____5499 = (

let uu____5500 = (

let uu____5509 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____5509))
in (uu____5500)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____5499))
in (uu____5494 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____5491))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env t))
in (

let uu____5532 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____5532) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____5543 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____5551) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____5567) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____5584 = ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))
in (match (uu____5584) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____5600))::((ens, uu____5602))::uu____5603 -> begin
(

let uu____5646 = (

let uu____5649 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____5649))
in (

let uu____5650 = (

let uu____5651 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____5651))
in ((uu____5646), (uu____5650))))
end
| uu____5654 -> begin
(

let uu____5665 = (

let uu____5671 = (

let uu____5673 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____5673))
in ((FStar_Errors.Fatal_EffectConstructorNotFullyApplied), (uu____5671)))
in (FStar_Errors.raise_error uu____5665 comp.FStar_Syntax_Syntax.pos))
end)
end
| uu____5683 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____5693))::uu____5694 -> begin
(

let uu____5721 = (

let uu____5726 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5726))
in (match (uu____5721) with
| (us_r, uu____5758) -> begin
(

let uu____5759 = (

let uu____5764 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5764))
in (match (uu____5759) with
| (us_e, uu____5796) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____5799 = (

let uu____5800 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar uu____5800 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5799 us_r))
in (

let as_ens = (

let uu____5802 = (

let uu____5803 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar uu____5803 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5802 us_e))
in (

let req = (

let uu____5807 = (

let uu____5812 = (

let uu____5813 = (

let uu____5824 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5824)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____5813)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____5812))
in (uu____5807 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____5864 = (

let uu____5869 = (

let uu____5870 = (

let uu____5881 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5881)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____5870)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____5869))
in (uu____5864 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____5918 = (

let uu____5921 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____5921))
in (

let uu____5922 = (

let uu____5923 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____5923))
in ((uu____5918), (uu____5922)))))))))
end))
end))
end
| uu____5926 -> begin
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

let uu____5960 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____5960) with
| true -> begin
(

let uu____5965 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____5967 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____5965 uu____5967)))
end
| uu____5970 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env tm)
in ((

let uu____6021 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____6021) with
| true -> begin
(

let uu____6026 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____6028 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____6026 uu____6028)))
end
| uu____6031 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____6039 = (

let uu____6041 = (

let uu____6042 = (FStar_Syntax_Subst.compress t)
in uu____6042.FStar_Syntax_Syntax.n)
in (match (uu____6041) with
| FStar_Syntax_Syntax.Tm_app (uu____6046) -> begin
false
end
| uu____6064 -> begin
true
end))
in (match (uu____6039) with
| true -> begin
t
end
| uu____6067 -> begin
(

let uu____6069 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6069) with
| (head1, args) -> begin
(

let uu____6112 = (

let uu____6114 = (

let uu____6115 = (FStar_Syntax_Subst.compress head1)
in uu____6115.FStar_Syntax_Syntax.n)
in (match (uu____6114) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____6120 -> begin
false
end))
in (match (uu____6112) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____6152 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____6164 -> begin
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
| uu____6196 -> begin
((

let uu____6199 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6199) with
| true -> begin
(

let uu____6202 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6204 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____6206 = (

let uu____6208 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Common.string_of_option FStar_Syntax_Print.term_to_string uu____6208))
in (FStar_Util.print3 "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n" uu____6202 uu____6204 uu____6206))))
end
| uu____6212 -> begin
()
end));
(

let number_of_implicits = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____6221 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____6221) with
| (formals, uu____6237) -> begin
(

let n_implicits = (

let uu____6259 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____6337 -> (match (uu____6337) with
| (uu____6345, imp) -> begin
((FStar_Option.isNone imp) || (

let uu____6352 = (FStar_Syntax_Util.eq_aqual imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)))
in (Prims.op_Equality uu____6352 FStar_Syntax_Util.Equal)))
end))))
in (match (uu____6259) with
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

let uu____6477 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____6477) with
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

let uu____6491 = (

let uu____6497 = (

let uu____6499 = (FStar_Util.string_of_int n_expected)
in (

let uu____6501 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6503 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____6499 uu____6501 uu____6503))))
in ((FStar_Errors.Fatal_MissingImplicitArguments), (uu____6497)))
in (

let uu____6507 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____6491 uu____6507)))
end
| uu____6511 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___7_6525 -> (match (uu___7_6525) with
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

let uu____6568 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6568) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_6699), uu____6686) when (_6699 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Env.trivial_guard))
end
| (uu____6732, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6734))))::rest) -> begin
(

let t2 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____6768 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t2)
in (match (uu____6768) with
| (v1, uu____6809, g) -> begin
((

let uu____6824 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____6824) with
| true -> begin
(

let uu____6827 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.print1 "maybe_instantiate: Instantiating implicit with %s\n" uu____6827))
end
| uu____6830 -> begin
()
end));
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____6837 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____6837) with
| (args, bs3, subst3, g') -> begin
(

let uu____6930 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::args), (bs3), (subst3), (uu____6930)))
end)));
)
end)))
end
| (uu____6957, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau))))::rest) -> begin
(

let t2 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____6994 = (

let uu____7007 = (

let uu____7014 = (

let uu____7019 = (FStar_Dyn.mkdyn env)
in ((uu____7019), (tau)))
in FStar_Pervasives_Native.Some (uu____7014))
in (FStar_TypeChecker_Env.new_implicit_var_aux "Instantiation of meta argument" e.FStar_Syntax_Syntax.pos env t2 FStar_Syntax_Syntax.Strict uu____7007))
in (match (uu____6994) with
| (v1, uu____7052, g) -> begin
((

let uu____7067 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____7067) with
| true -> begin
(

let uu____7070 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.print1 "maybe_instantiate: Instantiating meta argument with %s\n" uu____7070))
end
| uu____7073 -> begin
()
end));
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____7080 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____7080) with
| (args, bs3, subst3, g') -> begin
(

let uu____7173 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::args), (bs3), (subst3), (uu____7173)))
end)));
)
end)))
end
| (uu____7200, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Env.trivial_guard))
end))
in (

let uu____7248 = (

let uu____7275 = (inst_n_binders t1)
in (aux [] uu____7275 bs1))
in (match (uu____7248) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____7347) -> begin
((e), (torig), (guard))
end
| (uu____7378, []) when (

let uu____7409 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____7409))) -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____7411 -> begin
(

let t2 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____7439 -> begin
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
| uu____7452 -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end)))));
)
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____7464 = (

let uu____7468 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____7468 (FStar_List.map (fun u -> (

let uu____7480 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____7480 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____7464 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____7508 = (FStar_Util.set_is_empty x)
in (match (uu____7508) with
| true -> begin
[]
end
| uu____7513 -> begin
(

let s = (

let uu____7526 = (

let uu____7529 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____7529))
in (FStar_All.pipe_right uu____7526 FStar_Util.set_elements))
in ((

let uu____7545 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7545) with
| true -> begin
(

let uu____7550 = (

let uu____7552 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____7552))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____7550))
end
| uu____7556 -> begin
()
end));
(

let r = (

let uu____7561 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____7561))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____7600 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7600) with
| true -> begin
(

let uu____7605 = (

let uu____7607 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7607))
in (

let uu____7611 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____7613 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____7605 uu____7611 uu____7613))))
end
| uu____7616 -> begin
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

let uu____7643 = (FStar_Util.set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____7643 FStar_Util.set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____7682) -> begin
generalized_univ_names
end
| (uu____7689, []) -> begin
explicit_univ_names
end
| uu____7696 -> begin
(

let uu____7705 = (

let uu____7711 = (

let uu____7713 = (FStar_Syntax_Print.term_to_string t)
in (Prims.op_Hat "Generalized universe in a term containing explicit universe annotation : " uu____7713))
in ((FStar_Errors.Fatal_UnexpectedGeneralizedUniverse), (uu____7711)))
in (FStar_Errors.raise_error uu____7705 t.FStar_Syntax_Syntax.pos))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in ((

let uu____7735 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7735) with
| true -> begin
(

let uu____7740 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____7742 = (FStar_Syntax_Print.univ_names_to_string univnames1)
in (FStar_Util.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" uu____7740 uu____7742)))
end
| uu____7745 -> begin
()
end));
(

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____7751 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7751) with
| true -> begin
(

let uu____7756 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____7756))
end
| uu____7759 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____7765 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____7765) with
| true -> begin
(

let uu____7770 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____7772 = (FStar_Syntax_Print.univ_names_to_string gen1)
in (FStar_Util.print2 "After generalization, t: %s and univs: %s\n" uu____7770 uu____7772)))
end
| uu____7775 -> begin
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

let uu____7856 = (

let uu____7858 = (FStar_Util.for_all (fun uu____7872 -> (match (uu____7872) with
| (uu____7882, uu____7883, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____7858))
in (match (uu____7856) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7926 -> begin
(

let norm1 = (fun c -> ((

let uu____7935 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____7935) with
| true -> begin
(

let uu____7938 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____7938))
end
| uu____7941 -> begin
()
end));
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env c)
in ((

let uu____7945 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____7945) with
| true -> begin
(

let uu____7948 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7948))
end
| uu____7951 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____7966 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____7966 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____8000 -> (match (uu____8000) with
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

let uu____8037 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8037) with
| true -> begin
(

let uu____8042 = (

let uu____8044 = (

let uu____8048 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____8048 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8044 (FStar_String.concat ", ")))
in (

let uu____8096 = (

let uu____8098 = (

let uu____8102 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____8102 (FStar_List.map (fun u -> (

let uu____8115 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____8117 = (FStar_Syntax_Print.term_to_string u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____8115 uu____8117)))))))
in (FStar_All.pipe_right uu____8098 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8042 uu____8096)))
end
| uu____8126 -> begin
()
end));
(

let univs2 = (

let uu____8131 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uv -> (

let uu____8143 = (FStar_Syntax_Free.univs uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.set_union univs2 uu____8143))) univs1 uu____8131))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____8150 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____8150) with
| true -> begin
(

let uu____8155 = (

let uu____8157 = (

let uu____8161 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____8161 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____8157 (FStar_String.concat ", ")))
in (

let uu____8209 = (

let uu____8211 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> (

let uu____8225 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____8227 = (FStar_TypeChecker_Normalize.term_to_string env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____8225 uu____8227))))))
in (FStar_All.pipe_right uu____8211 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8155 uu____8209)))
end
| uu____8236 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
)))))
end))
in (

let uu____8248 = (

let uu____8265 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____8265))
in (match (uu____8248) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____8355 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____8355) with
| true -> begin
()
end
| uu____8358 -> begin
(

let uu____8360 = lec_hd
in (match (uu____8360) with
| (lb1, uu____8368, uu____8369) -> begin
(

let uu____8370 = lec2
in (match (uu____8370) with
| (lb2, uu____8378, uu____8379) -> begin
(

let msg = (

let uu____8382 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8384 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____8382 uu____8384)))
in (

let uu____8387 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleSetOfUniverse), (msg)) uu____8387)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun u -> (FStar_All.pipe_right u21 (FStar_Util.for_some (fun u' -> (FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head u'.FStar_Syntax_Syntax.ctx_uvar_head))))))))
in (

let uu____8455 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____8455) with
| true -> begin
()
end
| uu____8458 -> begin
(

let uu____8460 = lec_hd
in (match (uu____8460) with
| (lb1, uu____8468, uu____8469) -> begin
(

let uu____8470 = lec2
in (match (uu____8470) with
| (lb2, uu____8478, uu____8479) -> begin
(

let msg = (

let uu____8482 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____8484 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____8482 uu____8484)))
in (

let uu____8487 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleNumberOfTypes), (msg)) uu____8487)))
end))
end))
end))))
in (

let lecs1 = (

let uu____8498 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____8551 = (univs_and_uvars_of_lec this_lec)
in (match (uu____8551) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____8498 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail1 = (fun k -> (

let uu____8656 = lec_hd
in (match (uu____8656) with
| (lbname, e, c) -> begin
(

let uu____8666 = (

let uu____8672 = (

let uu____8674 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____8676 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____8678 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____8674 uu____8676 uu____8678))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____8672)))
in (

let uu____8682 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____8666 uu____8682)))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun u -> (

let uu____8701 = (FStar_Syntax_Unionfind.find u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____8701) with
| FStar_Pervasives_Native.Some (uu____8710) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____8718 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____8722 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8722) with
| (bs, kres) -> begin
((

let uu____8766 = (

let uu____8767 = (

let uu____8770 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____8770))
in uu____8767.FStar_Syntax_Syntax.n)
in (match (uu____8766) with
| FStar_Syntax_Syntax.Tm_type (uu____8771) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____8775 = (

let uu____8777 = (FStar_Util.set_is_empty free)
in (not (uu____8777)))
in (match (uu____8775) with
| true -> begin
(fail1 kres)
end
| uu____8780 -> begin
()
end)))
end
| uu____8782 -> begin
(fail1 kres)
end));
(

let a = (

let uu____8784 = (

let uu____8787 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _8790 -> FStar_Pervasives_Native.Some (_8790)) uu____8787))
in (FStar_Syntax_Syntax.new_bv uu____8784 kres))
in (

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Syntax.bv_to_name a)
end
| uu____8798 -> begin
(

let uu____8807 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____8807 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
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

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____8910 -> (match (uu____8910) with
| (lbname, e, c) -> begin
(

let uu____8956 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____9017 -> begin
(

let uu____9030 = ((e), (c))
in (match (uu____9030) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____9070 -> (match (uu____9070) with
| (x, uu____9076) -> begin
(

let uu____9077 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____9077))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____9095 = (

let uu____9097 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____9097))
in (match (uu____9095) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____9101 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____9103 -> begin
e1
end)
in (

let t = (

let uu____9106 = (

let uu____9107 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____9107.FStar_Syntax_Syntax.n)
in (match (uu____9106) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____9132 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____9132) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____9143 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____9147 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____9147), (gen_tvars))))))))
end))
end)
in (match (uu____8956) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____9294 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____9294) with
| true -> begin
(

let uu____9297 = (

let uu____9299 = (FStar_List.map (fun uu____9314 -> (match (uu____9314) with
| (lb, uu____9323, uu____9324) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____9299 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____9297))
end
| uu____9331 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____9350 -> (match (uu____9350) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____9379 = (gen env is_rec lecs)
in (match (uu____9379) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____9478 -> (match (uu____9478) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____9540 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____9540) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____9588 -> (match (uu____9588) with
| (l, us, e, c, gvs) -> begin
(

let uu____9622 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____9624 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____9626 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____9628 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____9630 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____9622 uu____9624 uu____9626 uu____9628 uu____9630))))))
end))))
end
| uu____9634 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____9675 -> (match (uu____9675) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____9719 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____9719), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check1 = (fun env2 t11 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t11 t21)
end
| uu____9778 -> begin
(

let uu____9780 = (FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21)
in (match (uu____9780) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____9786 = (FStar_TypeChecker_Env.apply_guard f e)
in (FStar_All.pipe_left (fun _9789 -> FStar_Pervasives_Native.Some (_9789)) uu____9786))
end))
end))
in (

let is_var = (fun e1 -> (

let uu____9797 = (

let uu____9798 = (FStar_Syntax_Subst.compress e1)
in uu____9798.FStar_Syntax_Syntax.n)
in (match (uu____9797) with
| FStar_Syntax_Syntax.Tm_name (uu____9802) -> begin
true
end
| uu____9804 -> begin
false
end)))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___1273_9825 = x
in {FStar_Syntax_Syntax.ppname = uu___1273_9825.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1273_9825.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____9826 -> begin
e2
end)))
in (

let env2 = (

let uu___1276_9828 = env1
in (

let uu____9829 = (env1.FStar_TypeChecker_Env.use_eq || (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = uu___1276_9828.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1276_9828.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1276_9828.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1276_9828.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1276_9828.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1276_9828.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1276_9828.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1276_9828.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1276_9828.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1276_9828.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1276_9828.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1276_9828.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1276_9828.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1276_9828.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1276_9828.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1276_9828.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1276_9828.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu____9829; FStar_TypeChecker_Env.is_iface = uu___1276_9828.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1276_9828.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___1276_9828.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___1276_9828.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1276_9828.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1276_9828.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1276_9828.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1276_9828.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1276_9828.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1276_9828.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1276_9828.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1276_9828.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1276_9828.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1276_9828.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1276_9828.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1276_9828.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1276_9828.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1276_9828.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1276_9828.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1276_9828.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1276_9828.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1276_9828.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1276_9828.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1276_9828.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1276_9828.FStar_TypeChecker_Env.nbe}))
in (

let uu____9831 = (check1 env2 t1 t2)
in (match (uu____9831) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9838 = (FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e t1)
in (

let uu____9844 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____9838 uu____9844)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____9851 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____9851) with
| true -> begin
(

let uu____9856 = (FStar_TypeChecker_Rel.guard_to_string env2 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____9856))
end
| uu____9860 -> begin
()
end));
(

let uu____9862 = (decorate e t2)
in ((uu____9862), (g)));
)
end))))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> ((

let uu____9890 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____9890) with
| true -> begin
(

let uu____9893 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "check_top_level, lc = %s\n" uu____9893))
end
| uu____9896 -> begin
()
end));
(

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_Syntax_Util.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____9907 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____9907) with
| true -> begin
(

let uu____9915 = (discharge g1)
in (

let uu____9917 = (FStar_Syntax_Syntax.lcomp_comp lc)
in ((uu____9915), (uu____9917))))
end
| uu____9919 -> begin
(

let c = (FStar_Syntax_Syntax.lcomp_comp lc)
in (

let steps = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]
in (

let c1 = (

let uu____9926 = (

let uu____9927 = (

let uu____9928 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____9928 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____9927 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right uu____9926 (FStar_TypeChecker_Env.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____9930 = (destruct_comp c1)
in (match (uu____9930) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____9948 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____9949 = (

let uu____9954 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (

let uu____9955 = (

let uu____9956 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____9965 = (

let uu____9976 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____9976)::[])
in (uu____9956)::uu____9965))
in (FStar_Syntax_Syntax.mk_Tm_app uu____9954 uu____9955)))
in (uu____9949 FStar_Pervasives_Native.None uu____9948)))
in ((

let uu____10010 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10010) with
| true -> begin
(

let uu____10015 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____10015))
end
| uu____10018 -> begin
()
end));
(

let g2 = (

let uu____10021 = (FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Env.conj_guard g1 uu____10021))
in (

let uu____10022 = (discharge g2)
in (

let uu____10024 = (FStar_Syntax_Syntax.mk_Comp c1)
in ((uu____10022), (uu____10024)))));
))
end))))))
end))));
))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___8_10058 -> (match (uu___8_10058) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____10068))::[] -> begin
(f fst1)
end
| uu____10093 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____10105 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____10105 (fun _10106 -> FStar_TypeChecker_Common.NonTrivial (_10106)))))
in (

let op_or_e = (fun e -> (

let uu____10117 = (

let uu____10118 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____10118))
in (FStar_All.pipe_right uu____10117 (fun _10121 -> FStar_TypeChecker_Common.NonTrivial (_10121)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _10128 -> FStar_TypeChecker_Common.NonTrivial (_10128))))
in (

let op_or_t = (fun t -> (

let uu____10139 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____10139 (fun _10142 -> FStar_TypeChecker_Common.NonTrivial (_10142)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _10149 -> FStar_TypeChecker_Common.NonTrivial (_10149))))
in (

let short_op_ite = (fun uu___9_10155 -> (match (uu___9_10155) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____10165))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____10192))::[] -> begin
(

let uu____10233 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____10233 (fun _10234 -> FStar_TypeChecker_Common.NonTrivial (_10234))))
end
| uu____10235 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____10247 = (

let uu____10255 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____10255)))
in (

let uu____10263 = (

let uu____10273 = (

let uu____10281 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____10281)))
in (

let uu____10289 = (

let uu____10299 = (

let uu____10307 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____10307)))
in (

let uu____10315 = (

let uu____10325 = (

let uu____10333 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____10333)))
in (

let uu____10341 = (

let uu____10351 = (

let uu____10359 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____10359)))
in (uu____10351)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____10325)::uu____10341))
in (uu____10299)::uu____10315))
in (uu____10273)::uu____10289))
in (uu____10247)::uu____10263))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____10421 = (FStar_Util.find_map table (fun uu____10436 -> (match (uu____10436) with
| (x, mk1) -> begin
(

let uu____10453 = (FStar_Ident.lid_equals x lid)
in (match (uu____10453) with
| true -> begin
(

let uu____10458 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____10458))
end
| uu____10459 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (uu____10421) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____10462 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____10470 = (

let uu____10471 = (FStar_Syntax_Util.un_uinst l)
in uu____10471.FStar_Syntax_Syntax.n)
in (match (uu____10470) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____10476 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____10512))::uu____10513 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____10532 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____10541, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10542))))::uu____10543 -> begin
bs
end
| uu____10561 -> begin
(

let uu____10562 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____10562) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____10566 = (

let uu____10567 = (FStar_Syntax_Subst.compress t)
in uu____10567.FStar_Syntax_Syntax.n)
in (match (uu____10566) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____10571) -> begin
(

let uu____10592 = (FStar_Util.prefix_until (fun uu___10_10632 -> (match (uu___10_10632) with
| (uu____10640, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10641))) -> begin
false
end
| uu____10646 -> begin
true
end)) bs')
in (match (uu____10592) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____10682, uu____10683) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____10755, uu____10756) -> begin
(

let uu____10829 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____10849 -> (match (uu____10849) with
| (x, uu____10858) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____10829) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____10907 -> (match (uu____10907) with
| (x, i) -> begin
(

let uu____10926 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____10926), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____10935 -> begin
bs
end))
end))
end
| uu____10937 -> begin
bs
end))
end))
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 t -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in (

let uu____10966 = (((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1)))
in (match (uu____10966) with
| true -> begin
e
end
| uu____10969 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end)))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____10997 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____10997) with
| true -> begin
e
end
| uu____11000 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____11040 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____11040) with
| true -> begin
((

let uu____11045 = (FStar_Ident.text_of_lid lident)
in (d uu____11045));
(

let uu____11047 = (FStar_Ident.text_of_lid lident)
in (

let uu____11049 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" uu____11047 uu____11049)));
)
end
| uu____11052 -> begin
()
end));
(

let fv = (

let uu____11055 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____11055 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (((FStar_Syntax_Util.mk_letbinding lbname [] FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def [] FStar_Range.dummyRange))::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____11067 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___1434_11069 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___1434_11069.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___1434_11069.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___1434_11069.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1434_11069.FStar_Syntax_Syntax.sigattrs})), (uu____11067)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (

let visibility = (fun uu___11_11087 -> (match (uu___11_11087) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11090 -> begin
false
end))
in (

let reducibility = (fun uu___12_11098 -> (match (uu___12_11098) with
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
| uu____11105 -> begin
false
end))
in (

let assumption = (fun uu___13_11113 -> (match (uu___13_11113) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____11117 -> begin
false
end))
in (

let reification = (fun uu___14_11125 -> (match (uu___14_11125) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____11128) -> begin
true
end
| uu____11130 -> begin
false
end))
in (

let inferred = (fun uu___15_11138 -> (match (uu___15_11138) with
| FStar_Syntax_Syntax.Discriminator (uu____11140) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____11142) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____11148) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____11158) -> begin
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
| uu____11171 -> begin
false
end))
in (

let has_eq = (fun uu___16_11179 -> (match (uu___16_11179) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____11183 -> begin
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
| FStar_Syntax_Syntax.Reflectable (uu____11262) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11269 -> begin
true
end))
in (

let quals = (FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se) (FStar_List.filter (fun x -> (not ((Prims.op_Equality x FStar_Syntax_Syntax.Logic))))))
in (

let uu____11280 = (

let uu____11282 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___17_11288 -> (match (uu___17_11288) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____11291 -> begin
false
end))))
in (FStar_All.pipe_right uu____11282 Prims.op_Negation))
in (match (uu____11280) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____11312 = (

let uu____11318 = (

let uu____11320 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____11320 msg))
in ((FStar_Errors.Fatal_QulifierListNotPermitted), (uu____11318)))
in (FStar_Errors.raise_error uu____11312 r)))
in (

let err = (fun msg -> (err' (Prims.op_Hat ": " msg)))
in (

let err'1 = (fun uu____11338 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____11343 -> begin
()
end);
(

let uu____11346 = (

let uu____11348 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____11348)))
in (match (uu____11346) with
| true -> begin
(err "ill-formed combination")
end
| uu____11355 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____11358), uu____11359) -> begin
((

let uu____11371 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____11371) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____11378 -> begin
()
end));
(

let uu____11380 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____11380) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____11389 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____11391) -> begin
(

let uu____11400 = (

let uu____11402 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____11402)))
in (match (uu____11400) with
| true -> begin
(err'1 ())
end
| uu____11410 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____11412) -> begin
(

let uu____11419 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____11419) with
| true -> begin
(err'1 ())
end
| uu____11425 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____11427) -> begin
(

let uu____11434 = (

let uu____11436 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____11436)))
in (match (uu____11434) with
| true -> begin
(err'1 ())
end
| uu____11444 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____11446) -> begin
(

let uu____11447 = (

let uu____11449 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11449)))
in (match (uu____11447) with
| true -> begin
(err'1 ())
end
| uu____11457 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____11459) -> begin
(

let uu____11460 = (

let uu____11462 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____11462)))
in (match (uu____11460) with
| true -> begin
(err'1 ())
end
| uu____11470 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____11472) -> begin
(

let uu____11485 = (

let uu____11487 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____11487)))
in (match (uu____11485) with
| true -> begin
(err'1 ())
end
| uu____11495 -> begin
()
end))
end
| uu____11497 -> begin
()
end);
))))))
end
| uu____11498 -> begin
()
end)))))))))))


let must_erase_for_extraction : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun g t -> (

let has_erased_for_extraction_attr = (fun fv -> (

let uu____11520 = (

let uu____11525 = (FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv)
in (FStar_All.pipe_right uu____11525 (FStar_TypeChecker_Env.lookup_attrs_of_lid g)))
in (FStar_All.pipe_right uu____11520 (fun l_opt -> ((FStar_Util.is_some l_opt) && (

let uu____11544 = (FStar_All.pipe_right l_opt FStar_Util.must)
in (FStar_All.pipe_right uu____11544 (FStar_List.existsb (fun t1 -> (

let uu____11562 = (

let uu____11563 = (FStar_Syntax_Subst.compress t1)
in uu____11563.FStar_Syntax_Syntax.n)
in (match (uu____11562) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (FStar_Ident.lid_equals fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.must_erase_for_extraction_attr) -> begin
true
end
| uu____11569 -> begin
false
end)))))))))))
in (

let rec aux_whnf = (fun env t1 -> (

let uu____11595 = (

let uu____11596 = (FStar_Syntax_Subst.compress t1)
in uu____11596.FStar_Syntax_Syntax.n)
in (match (uu____11595) with
| FStar_Syntax_Syntax.Tm_type (uu____11600) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (has_erased_for_extraction_attr fv))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____11603) -> begin
(

let uu____11618 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____11618) with
| (bs, c) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____11651 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____11651) with
| true -> begin
(aux env1 (FStar_Syntax_Util.comp_result c))
end
| uu____11655 -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____11657; FStar_Syntax_Syntax.index = uu____11658; FStar_Syntax_Syntax.sort = t2}, uu____11660) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____11669, uu____11670) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____11712)::[]) -> begin
(

let uu____11751 = (

let uu____11752 = (FStar_Syntax_Util.un_uinst head1)
in uu____11752.FStar_Syntax_Syntax.n)
in (match (uu____11751) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid) || (has_erased_for_extraction_attr fv))
end
| uu____11757 -> begin
false
end))
end
| uu____11759 -> begin
false
end)))
and aux = (fun env t1 -> (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::[]) env t1)
in (

let res = (aux_whnf env t2)
in ((

let uu____11769 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Extraction")))
in (match (uu____11769) with
| true -> begin
(

let uu____11774 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "must_erase=%s: %s\n" (match (res) with
| true -> begin
"true"
end
| uu____11780 -> begin
"false"
end) uu____11774))
end
| uu____11783 -> begin
()
end));
res;
))))
in (aux g t))))




