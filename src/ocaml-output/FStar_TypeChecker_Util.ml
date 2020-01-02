
open Prims
open FStar_Pervasives

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_TypeChecker_Common.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  unit = (fun env errs -> (

let uu____22 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____23 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.log_issue uu____22 uu____23))))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Common.guard_t) = (fun reason r env k -> (FStar_TypeChecker_Env.new_implicit_var_aux reason r env k FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None))


let close_guard_implicits : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun env solve_deferred xs g -> (

let uu____91 = ((FStar_Options.eager_subtyping ()) || solve_deferred)
in (match (uu____91) with
| true -> begin
(

let uu____94 = (FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred (FStar_List.partition (fun uu____146 -> (match (uu____146) with
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

let uu___49_248 = g
in {FStar_TypeChecker_Common.guard_f = uu___49_248.FStar_TypeChecker_Common.guard_f; FStar_TypeChecker_Common.deferred = solve_now; FStar_TypeChecker_Common.univ_ineqs = uu___49_248.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___49_248.FStar_TypeChecker_Common.implicits}))
in (

let g2 = (

let uu___52_250 = g1
in {FStar_TypeChecker_Common.guard_f = uu___52_250.FStar_TypeChecker_Common.guard_f; FStar_TypeChecker_Common.deferred = defer; FStar_TypeChecker_Common.univ_ineqs = uu___52_250.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___52_250.FStar_TypeChecker_Common.implicits})
in g2));
)
end))
end
| uu____251 -> begin
g
end)))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in (

let uu____267 = (

let uu____269 = (FStar_Util.set_is_empty uvs)
in (not (uu____269)))
in (match (uu____267) with
| true -> begin
(

let us = (

let uu____274 = (

let uu____278 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun u -> (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)) uu____278))
in (FStar_All.pipe_right uu____274 (FStar_String.concat ", ")))
in ((FStar_Options.push ());
(FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____297 = (

let uu____303 = (

let uu____305 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us uu____305))
in ((FStar_Errors.Error_UncontrainedUnificationVar), (uu____303)))
in (FStar_Errors.log_issue r uu____297));
(FStar_Options.pop ());
))
end
| uu____309 -> begin
()
end))))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env uu____328 -> (match (uu____328) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____339; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____341; FStar_Syntax_Syntax.lbpos = uu____342} -> begin
(

let rng = (FStar_Syntax_Syntax.range_of_lbname lbname)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____377 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 e)
in (match (uu____377) with
| (univ_vars2, e1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars2)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let rec aux = (fun e2 -> (

let e3 = (FStar_Syntax_Subst.compress e2)
in (match (e3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e4, uu____415) -> begin
(aux e4)
end
| FStar_Syntax_Syntax.Tm_ascribed (e4, t2, uu____422) -> begin
(FStar_Pervasives_Native.fst t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____477) -> begin
(

let res = (aux body)
in (

let c = (match (res) with
| FStar_Util.Inl (t2) -> begin
(

let uu____513 = (FStar_Options.ml_ish ())
in (match (uu____513) with
| true -> begin
(FStar_Syntax_Util.ml_comp t2 r)
end
| uu____518 -> begin
(FStar_Syntax_Syntax.mk_Total t2)
end))
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in ((

let uu____535 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____535) with
| true -> begin
(

let uu____538 = (FStar_Range.string_of_range r)
in (

let uu____540 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Using type %s\n" uu____538 uu____540)))
end
| uu____543 -> begin
()
end));
FStar_Util.Inl (t2);
))))
end
| uu____545 -> begin
FStar_Util.Inl (FStar_Syntax_Syntax.tun)
end)))
in (

let t2 = (

let uu____547 = (aux e1)
in (match (uu____547) with
| FStar_Util.Inr (c) -> begin
(

let uu____553 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____553) with
| true -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____556 -> begin
(

let uu____558 = (

let uu____564 = (

let uu____566 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" uu____566))
in ((FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec), (uu____564)))
in (FStar_Errors.raise_error uu____558 rng))
end))
end
| FStar_Util.Inl (t2) -> begin
t2
end))
in ((univ_vars2), (t2), (true))))))
end))
end
| uu____575 -> begin
(

let uu____576 = (FStar_Syntax_Subst.open_univ_vars univ_vars1 t1)
in (match (uu____576) with
| (univ_vars2, t2) -> begin
((univ_vars2), (t2), (false))
end))
end)))
end))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let mk1 = (fun f -> (FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun uu____640 -> (match (uu____640) with
| (p, i) -> begin
(

let uu____660 = (decorated_pattern_as_term p)
in (match (uu____660) with
| (vars, te) -> begin
(

let uu____683 = (

let uu____688 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (uu____688)))
in ((vars), (uu____683)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____702 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (uu____702)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____706 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____706)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____710 = (mk1 (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (uu____710)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____733 = (

let uu____752 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right uu____752 FStar_List.unzip))
in (match (uu____733) with
| (vars, args) -> begin
(

let vars1 = (FStar_List.flatten vars)
in (

let uu____890 = (

let uu____891 = (

let uu____892 = (

let uu____909 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((uu____909), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____892))
in (mk1 uu____891))
in ((vars1), (uu____890))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end))))


let comp_univ_opt : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____948, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.GTotal (uu____958, uopt) -> begin
uopt
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::uu____972 -> begin
FStar_Pervasives_Native.Some (hd1)
end)
end))


let lcomp_univ_opt : FStar_TypeChecker_Common.lcomp  ->  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option * FStar_TypeChecker_Common.guard_t) = (fun lc -> (

let uu____987 = (FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp)
in (FStar_All.pipe_right uu____987 (fun uu____1015 -> (match (uu____1015) with
| (c, g) -> begin
(((comp_univ_opt c)), (g))
end)))))


let destruct_wp_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (FStar_Syntax_Util.destruct_comp c))


let lift_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_TypeChecker_Env.mlift  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env c lift -> (

let uu____1078 = (FStar_All.pipe_right (

let uu___169_1080 = c
in {FStar_Syntax_Syntax.comp_univs = uu___169_1080.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___169_1080.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___169_1080.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___169_1080.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = []}) FStar_Syntax_Syntax.mk_Comp)
in (FStar_All.pipe_right uu____1078 (lift.FStar_TypeChecker_Env.mlift_wp env))))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let uu____1101 = (

let uu____1108 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (

let uu____1109 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env uu____1108 uu____1109)))
in (match (uu____1101) with
| (m, uu____1111, uu____1112) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> (

let uu____1129 = ((FStar_TypeChecker_Common.is_total_lcomp c1) && (FStar_TypeChecker_Common.is_total_lcomp c2))
in (match (uu____1129) with
| true -> begin
FStar_Parser_Const.effect_Tot_lid
end
| uu____1132 -> begin
(join_effects env c1.FStar_TypeChecker_Common.eff_name c2.FStar_TypeChecker_Common.eff_name)
end)))


let lift_comps : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  Prims.bool  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env c1 c2 b b_maybe_free_in_c2 -> (

let c11 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c21 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in (

let uu____1184 = (FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____1184) with
| (m, lift1, lift2) -> begin
(

let uu____1202 = (lift_comp env c11 lift1)
in (match (uu____1202) with
| (c12, g1) -> begin
(

let uu____1217 = (match ((not (b_maybe_free_in_c2))) with
| true -> begin
(lift_comp env c21 lift2)
end
| uu____1227 -> begin
(

let x_a = (match (b) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.null_binder (FStar_Syntax_Util.comp_result c12))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Syntax.mk_binder x)
end)
in (

let env_x = (FStar_TypeChecker_Env.push_binders env ((x_a)::[]))
in (

let uu____1256 = (lift_comp env_x c21 lift2)
in (match (uu____1256) with
| (c22, g2) -> begin
(

let uu____1267 = (FStar_TypeChecker_Env.close_guard env ((x_a)::[]) g2)
in ((c22), (uu____1267)))
end))))
end)
in (match (uu____1217) with
| (c22, g2) -> begin
(

let uu____1290 = (FStar_TypeChecker_Env.conj_guard g1 g2)
in ((m), (c12), (c22), (uu____1290)))
end))
end))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l1 = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (

let uu____1351 = (

let uu____1352 = (

let uu____1363 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1363)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = uu____1352; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp uu____1351)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> (

let uu____1447 = (FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid)
in (match (uu____1447) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' result (FStar_Pervasives_Native.Some (u_result)))
end
| uu____1450 -> begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end)))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1459 = (

let uu____1460 = (FStar_Syntax_Subst.compress t)
in uu____1460.FStar_Syntax_Syntax.n)
in (match (uu____1459) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1464) -> begin
true
end
| uu____1480 -> begin
false
end)))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (reason1) -> begin
(

let uu____1550 = (

let uu____1552 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation uu____1552))
in (match (uu____1550) with
| true -> begin
f
end
| uu____1557 -> begin
(

let uu____1559 = (reason1 ())
in (label uu____1559 r f))
end))
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___246_1580 = g
in (

let uu____1581 = (

let uu____1582 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (uu____1582))
in {FStar_TypeChecker_Common.guard_f = uu____1581; FStar_TypeChecker_Common.deferred = uu___246_1580.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___246_1580.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___246_1580.FStar_TypeChecker_Common.implicits}))
end))


let close_wp_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env bvs c -> (

let uu____1603 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____1603) with
| true -> begin
c
end
| uu____1606 -> begin
(

let uu____1608 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____1608) with
| true -> begin
c
end
| uu____1611 -> begin
(

let close_wp = (fun u_res md res_t bvs1 wp0 -> (

let close1 = (

let uu____1650 = (FStar_All.pipe_right md FStar_Syntax_Util.get_wp_close_combinator)
in (FStar_All.pipe_right uu____1650 FStar_Util.must))
in (FStar_List.fold_right (fun x wp -> (

let bs = (

let uu____1678 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1678)::[])
in (

let us = (

let uu____1700 = (

let uu____1703 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (uu____1703)::[])
in (u_res)::uu____1700)
in (

let wp1 = (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))
in (

let uu____1709 = (

let uu____1714 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md close1)
in (

let uu____1715 = (

let uu____1716 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____1725 = (

let uu____1736 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (

let uu____1745 = (

let uu____1756 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____1756)::[])
in (uu____1736)::uu____1745))
in (uu____1716)::uu____1725))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1714 uu____1715)))
in (uu____1709 FStar_Pervasives_Native.None wp0.FStar_Syntax_Syntax.pos)))))) bvs1 wp0)))
in (

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let uu____1798 = (destruct_wp_comp c1)
in (match (uu____1798) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (

let wp1 = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1 c1.FStar_Syntax_Syntax.flags)))
end))))
end))
end)))


let close_wp_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_TypeChecker_Common.lcomp = (fun env bvs lc -> (

let bs = (FStar_All.pipe_right bvs (FStar_List.map FStar_Syntax_Syntax.mk_binder))
in (FStar_All.pipe_right lc (FStar_TypeChecker_Common.apply_lcomp (close_wp_comp env bvs) (fun g -> (

let uu____1838 = (FStar_All.pipe_right g (FStar_TypeChecker_Env.close_guard env bs))
in (FStar_All.pipe_right uu____1838 (close_guard_implicits env false bs))))))))


let close_layered_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_TypeChecker_Common.lcomp = (fun env bvs tms lc -> (

let bs = (FStar_All.pipe_right bvs (FStar_List.map FStar_Syntax_Syntax.mk_binder))
in (

let substs = (FStar_List.map2 (fun bv tm -> FStar_Syntax_Syntax.NT (((bv), (tm)))) bvs tms)
in (FStar_All.pipe_right lc (FStar_TypeChecker_Common.apply_lcomp (FStar_Syntax_Subst.subst_comp substs) (fun g -> (

let uu____1888 = (FStar_All.pipe_right g (FStar_TypeChecker_Env.close_guard env bs))
in (FStar_All.pipe_right uu____1888 (close_guard_implicits env false bs)))))))))


let should_not_inline_lc : FStar_TypeChecker_Common.lcomp  ->  Prims.bool = (fun lc -> (FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags (FStar_Util.for_some (fun uu___0_1901 -> (match (uu___0_1901) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____1904 -> begin
false
end)))))


let should_return : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Common.lcomp  ->  Prims.bool = (fun env eopt lc -> (

let lc_is_unit_or_effectful = (

let uu____1929 = (

let uu____1932 = (FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ FStar_Syntax_Util.arrow_formals_comp)
in (FStar_All.pipe_right uu____1932 FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____1929 (fun c -> ((

let uu____1988 = (FStar_TypeChecker_Env.is_reifiable_comp env c)
in (not (uu____1988))) && ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Util.is_unit) || (

let uu____1992 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____1992))))))))
in (match (eopt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (e) -> begin
((((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) && (not (lc_is_unit_or_effectful))) && (

let uu____2003 = (FStar_Syntax_Util.head_and_args' e)
in (match (uu____2003) with
| (head1, uu____2020) -> begin
(

let uu____2041 = (

let uu____2042 = (FStar_Syntax_Util.un_uinst head1)
in uu____2042.FStar_Syntax_Syntax.n)
in (match (uu____2041) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2047 = (

let uu____2049 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.is_irreducible env uu____2049))
in (not (uu____2047)))
end
| uu____2050 -> begin
true
end))
end))) && (

let uu____2053 = (should_not_inline_lc lc)
in (not (uu____2053))))
end)))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env u_t_opt t v1 -> (

let c = (

let uu____2081 = (

let uu____2083 = (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation uu____2083))
in (match (uu____2081) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____2088 -> begin
(

let uu____2090 = (FStar_Syntax_Util.is_unit t)
in (match (uu____2090) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero)))
end
| uu____2093 -> begin
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

let uu____2099 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____2099) with
| true -> begin
FStar_Syntax_Syntax.tun
end
| uu____2102 -> begin
(

let uu____2104 = (FStar_TypeChecker_Env.wp_signature env FStar_Parser_Const.effect_PURE_lid)
in (match (uu____2104) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let ret_wp = (FStar_All.pipe_right m FStar_Syntax_Util.get_return_vc_combinator)
in (

let uu____2115 = (

let uu____2116 = (

let uu____2121 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m ret_wp)
in (

let uu____2122 = (

let uu____2123 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____2132 = (

let uu____2143 = (FStar_Syntax_Syntax.as_arg v1)
in (uu____2143)::[])
in (uu____2123)::uu____2132))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2121 uu____2122)))
in (uu____2116 FStar_Pervasives_Native.None v1.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::[]) env uu____2115))))
end))
end))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end))
end))
in ((

let uu____2177 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return")))
in (match (uu____2177) with
| true -> begin
(

let uu____2182 = (FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos)
in (

let uu____2184 = (FStar_Syntax_Print.term_to_string v1)
in (

let uu____2186 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2182 uu____2184 uu____2186))))
end
| uu____2189 -> begin
()
end));
c;
)))


let mk_layered_bind : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env m ct1 b ct2 flags r1 -> ((

let uu____2244 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____2244) with
| true -> begin
(

let uu____2249 = (

let uu____2251 = (FStar_Syntax_Syntax.mk_Comp ct1)
in (FStar_Syntax_Print.comp_to_string uu____2251))
in (

let uu____2252 = (

let uu____2254 = (FStar_Syntax_Syntax.mk_Comp ct2)
in (FStar_Syntax_Print.comp_to_string uu____2254))
in (FStar_Util.print2 "Binding c1:%s and c2:%s {\n" uu____2249 uu____2252)))
end
| uu____2256 -> begin
()
end));
(

let ed = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____2259 = (

let uu____2270 = (FStar_List.hd ct1.FStar_Syntax_Syntax.comp_univs)
in (

let uu____2271 = (FStar_List.map FStar_Pervasives_Native.fst ct1.FStar_Syntax_Syntax.effect_args)
in ((uu____2270), (ct1.FStar_Syntax_Syntax.result_typ), (uu____2271))))
in (match (uu____2259) with
| (u1, t1, is1) -> begin
(

let uu____2305 = (

let uu____2316 = (FStar_List.hd ct2.FStar_Syntax_Syntax.comp_univs)
in (

let uu____2317 = (FStar_List.map FStar_Pervasives_Native.fst ct2.FStar_Syntax_Syntax.effect_args)
in ((uu____2316), (ct2.FStar_Syntax_Syntax.result_typ), (uu____2317))))
in (match (uu____2305) with
| (u2, t2, is2) -> begin
(

let uu____2351 = (

let uu____2356 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_vc_combinator)
in (FStar_TypeChecker_Env.inst_tscheme_with uu____2356 ((u1)::(u2)::[])))
in (match (uu____2351) with
| (uu____2361, bind_t) -> begin
(

let bind_t_shape_error = (fun s -> (

let uu____2376 = (

let uu____2378 = (FStar_Syntax_Print.term_to_string bind_t)
in (FStar_Util.format2 "bind %s does not have proper shape (reason:%s)" uu____2378 s))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____2376))))
in (

let uu____2382 = (

let uu____2427 = (

let uu____2428 = (FStar_Syntax_Subst.compress bind_t)
in uu____2428.FStar_Syntax_Syntax.n)
in (match (uu____2427) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_List.length bs) >= (Prims.parse_int "4")) -> begin
(

let uu____2504 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2504) with
| ((a_b)::(b_b)::bs1, c1) -> begin
(

let uu____2589 = (

let uu____2616 = (FStar_List.splitAt ((FStar_List.length bs1) - (Prims.parse_int "2")) bs1)
in (FStar_All.pipe_right uu____2616 (fun uu____2701 -> (match (uu____2701) with
| (l1, l2) -> begin
(

let uu____2782 = (FStar_List.hd l2)
in (

let uu____2795 = (

let uu____2802 = (FStar_List.tl l2)
in (FStar_List.hd uu____2802))
in ((l1), (uu____2782), (uu____2795))))
end))))
in (match (uu____2589) with
| (rest_bs, f_b, g_b) -> begin
(

let uu____2930 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in ((a_b), (b_b), (rest_bs), (f_b), (g_b), (uu____2930)))
end))
end))
end
| uu____2963 -> begin
(

let uu____2964 = (bind_t_shape_error "Either not an arrow or not enough binders")
in (FStar_Errors.raise_error uu____2964 r1))
end))
in (match (uu____2382) with
| (a_b, b_b, rest_bs, f_b, g_b, bind_ct) -> begin
(

let uu____3089 = (

let uu____3096 = (

let uu____3097 = (

let uu____3098 = (

let uu____3105 = (FStar_All.pipe_right a_b FStar_Pervasives_Native.fst)
in ((uu____3105), (t1)))
in FStar_Syntax_Syntax.NT (uu____3098))
in (

let uu____3116 = (

let uu____3119 = (

let uu____3120 = (

let uu____3127 = (FStar_All.pipe_right b_b FStar_Pervasives_Native.fst)
in ((uu____3127), (t2)))
in FStar_Syntax_Syntax.NT (uu____3120))
in (uu____3119)::[])
in (uu____3097)::uu____3116))
in (FStar_TypeChecker_Env.uvars_for_binders env rest_bs uu____3096 (fun b1 -> (

let uu____3142 = (FStar_Syntax_Print.binder_to_string b1)
in (

let uu____3144 = (FStar_Range.string_of_range r1)
in (FStar_Util.format3 "implicit var for binder %s of %s:bind at %s" uu____3142 ed.FStar_Syntax_Syntax.mname.FStar_Ident.str uu____3144)))) r1))
in (match (uu____3089) with
| (rest_bs_uvars, g_uvars) -> begin
(

let subst1 = (FStar_List.map2 (fun b1 t -> (

let uu____3181 = (

let uu____3188 = (FStar_All.pipe_right b1 FStar_Pervasives_Native.fst)
in ((uu____3188), (t)))
in FStar_Syntax_Syntax.NT (uu____3181))) ((a_b)::(b_b)::rest_bs) ((t1)::(t2)::rest_bs_uvars))
in (

let f_guard = (

let f_sort_is = (

let uu____3215 = (

let uu____3216 = (

let uu____3219 = (

let uu____3220 = (FStar_All.pipe_right f_b FStar_Pervasives_Native.fst)
in uu____3220.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Subst.compress uu____3219))
in uu____3216.FStar_Syntax_Syntax.n)
in (match (uu____3215) with
| FStar_Syntax_Syntax.Tm_app (uu____3231, (uu____3232)::is) -> begin
(

let uu____3274 = (FStar_All.pipe_right is (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____3274 (FStar_List.map (FStar_Syntax_Subst.subst subst1))))
end
| uu____3307 -> begin
(

let uu____3308 = (bind_t_shape_error "f\'s type is not a repr type")
in (FStar_Errors.raise_error uu____3308 r1))
end))
in (FStar_List.fold_left2 (fun g i1 f_i1 -> (

let uu____3324 = (FStar_TypeChecker_Rel.teq env i1 f_i1)
in (FStar_TypeChecker_Env.conj_guard g uu____3324))) FStar_TypeChecker_Env.trivial_guard is1 f_sort_is))
in (

let g_guard = (

let x_a = (match (b) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.null_binder ct1.FStar_Syntax_Syntax.result_typ)
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Syntax.mk_binder x)
end)
in (

let g_sort_is = (

let uu____3343 = (

let uu____3344 = (

let uu____3347 = (

let uu____3348 = (FStar_All.pipe_right g_b FStar_Pervasives_Native.fst)
in uu____3348.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Subst.compress uu____3347))
in uu____3344.FStar_Syntax_Syntax.n)
in (match (uu____3343) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3381 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3381) with
| (bs1, c1) -> begin
(

let bs_subst = (

let uu____3391 = (

let uu____3398 = (

let uu____3399 = (FStar_List.hd bs1)
in (FStar_All.pipe_right uu____3399 FStar_Pervasives_Native.fst))
in (

let uu____3420 = (

let uu____3423 = (FStar_All.pipe_right x_a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____3423 FStar_Syntax_Syntax.bv_to_name))
in ((uu____3398), (uu____3420))))
in FStar_Syntax_Syntax.NT (uu____3391))
in (

let c2 = (FStar_Syntax_Subst.subst_comp ((bs_subst)::[]) c1)
in (

let uu____3437 = (

let uu____3438 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c2))
in uu____3438.FStar_Syntax_Syntax.n)
in (match (uu____3437) with
| FStar_Syntax_Syntax.Tm_app (uu____3443, (uu____3444)::is) -> begin
(

let uu____3486 = (FStar_All.pipe_right is (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____3486 (FStar_List.map (FStar_Syntax_Subst.subst subst1))))
end
| uu____3519 -> begin
(

let uu____3520 = (bind_t_shape_error "g\'s type is not a repr type")
in (FStar_Errors.raise_error uu____3520 r1))
end))))
end))
end
| uu____3529 -> begin
(

let uu____3530 = (bind_t_shape_error "g\'s type is not an arrow")
in (FStar_Errors.raise_error uu____3530 r1))
end))
in (

let env_g = (FStar_TypeChecker_Env.push_binders env ((x_a)::[]))
in (

let uu____3552 = (FStar_List.fold_left2 (fun g i1 g_i1 -> (

let uu____3560 = (FStar_TypeChecker_Rel.teq env_g i1 g_i1)
in (FStar_TypeChecker_Env.conj_guard g uu____3560))) FStar_TypeChecker_Env.trivial_guard is2 g_sort_is)
in (FStar_All.pipe_right uu____3552 (FStar_TypeChecker_Env.close_guard env ((x_a)::[])))))))
in (

let is = (

let uu____3576 = (

let uu____3577 = (FStar_Syntax_Subst.compress bind_ct.FStar_Syntax_Syntax.result_typ)
in uu____3577.FStar_Syntax_Syntax.n)
in (match (uu____3576) with
| FStar_Syntax_Syntax.Tm_app (uu____3582, (uu____3583)::is) -> begin
(

let uu____3625 = (FStar_All.pipe_right is (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____3625 (FStar_List.map (FStar_Syntax_Subst.subst subst1))))
end
| uu____3658 -> begin
(

let uu____3659 = (bind_t_shape_error "return type is not a repr type")
in (FStar_Errors.raise_error uu____3659 r1))
end))
in (

let c = (

let uu____3669 = (

let uu____3670 = (FStar_List.map FStar_Syntax_Syntax.as_arg is)
in {FStar_Syntax_Syntax.comp_univs = ct2.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = t2; FStar_Syntax_Syntax.effect_args = uu____3670; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp uu____3669))
in ((

let uu____3690 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____3690) with
| true -> begin
(

let uu____3695 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "} c after bind: %s\n" uu____3695))
end
| uu____3698 -> begin
()
end));
(

let uu____3700 = (FStar_TypeChecker_Env.conj_guards ((g_uvars)::(f_guard)::(g_guard)::[]))
in ((c), (uu____3700)));
))))))
end))
end)))
end))
end))
end)));
))


let mk_non_layered_bind : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun env m ct1 b ct2 flags r1 -> (

let uu____3745 = (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____3771 = (FStar_TypeChecker_Env.wp_signature env m)
in (match (uu____3771) with
| (a, kwp) -> begin
(

let uu____3802 = (destruct_wp_comp ct1)
in (

let uu____3809 = (destruct_wp_comp ct2)
in ((((md), (a), (kwp))), (uu____3802), (uu____3809))))
end)))
in (match (uu____3745) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3862 = (FStar_Syntax_Syntax.null_binder t1)
in (uu____3862)::[])
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____3882 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3882)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (

let r11 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) FStar_Pervasives_Native.None r1)
in (

let wp_args = (

let uu____3929 = (FStar_Syntax_Syntax.as_arg r11)
in (

let uu____3938 = (

let uu____3949 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____3958 = (

let uu____3969 = (FStar_Syntax_Syntax.as_arg t2)
in (

let uu____3978 = (

let uu____3989 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____3998 = (

let uu____4009 = (

let uu____4018 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg uu____4018))
in (uu____4009)::[])
in (uu____3989)::uu____3998))
in (uu____3969)::uu____3978))
in (uu____3949)::uu____3958))
in (uu____3929)::uu____3938))
in (

let bind_wp = (FStar_All.pipe_right md FStar_Syntax_Util.get_bind_vc_combinator)
in (

let wp = (

let uu____4071 = (

let uu____4076 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app uu____4076 wp_args))
in (uu____4071 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in (mk_comp md u_t2 t2 wp flags)))))))
end)))


let mk_bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env c1 b c2 flags r1 -> (

let uu____4124 = (lift_comps env c1 c2 b true)
in (match (uu____4124) with
| (m, c11, c21, g_lift) -> begin
(

let uu____4142 = (

let uu____4147 = (FStar_Syntax_Util.comp_to_comp_typ c11)
in (

let uu____4148 = (FStar_Syntax_Util.comp_to_comp_typ c21)
in ((uu____4147), (uu____4148))))
in (match (uu____4142) with
| (ct1, ct2) -> begin
(

let uu____4155 = (

let uu____4160 = (FStar_TypeChecker_Env.is_layered_effect env m)
in (match (uu____4160) with
| true -> begin
(mk_layered_bind env m ct1 b ct2 flags r1)
end
| uu____4167 -> begin
(

let uu____4169 = (mk_non_layered_bind env m ct1 b ct2 flags r1)
in ((uu____4169), (FStar_TypeChecker_Env.trivial_guard)))
end))
in (match (uu____4155) with
| (c, g_bind) -> begin
(

let uu____4176 = (FStar_TypeChecker_Env.conj_guard g_lift g_bind)
in ((c), (uu____4176)))
end))
end))
end)))


let bind_pure_wp_with : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env wp1 c flags -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let pure_c = (

let uu____4212 = (

let uu____4213 = (

let uu____4224 = (FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg)
in (uu____4224)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit; FStar_Syntax_Syntax.effect_args = uu____4213; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____4212))
in (mk_bind env pure_c FStar_Pervasives_Native.None c flags r))))


let weaken_flags : FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun flags -> (

let uu____4269 = (FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___1_4275 -> (match (uu___1_4275) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____4278 -> begin
false
end))))
in (match (uu____4269) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____4283 -> begin
(FStar_All.pipe_right flags (FStar_List.collect (fun uu___2_4290 -> (match (uu___2_4290) with
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


let weaken_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env c formula -> (

let uu____4318 = (FStar_Syntax_Util.is_ml_comp c)
in (match (uu____4318) with
| true -> begin
((c), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____4325 -> begin
(

let ct = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (

let pure_assume_wp = (

let uu____4329 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.pure_assume_wp_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____4329))
in (

let pure_assume_wp1 = (

let uu____4334 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4335 = (

let uu____4340 = (

let uu____4341 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula)
in (uu____4341)::[])
in (FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4340))
in (uu____4335 FStar_Pervasives_Native.None uu____4334)))
in (

let uu____4374 = (weaken_flags ct.FStar_Syntax_Syntax.flags)
in (bind_pure_wp_with env pure_assume_wp1 c uu____4374)))))
end)))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.lcomp = (fun env lc f -> (

let weaken = (fun uu____4402 -> (

let uu____4403 = (FStar_TypeChecker_Common.lcomp_comp lc)
in (match (uu____4403) with
| (c, g_c) -> begin
(

let uu____4414 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____4414) with
| true -> begin
((c), (g_c))
end
| uu____4421 -> begin
(match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
((c), (g_c))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____4428 = (weaken_comp env c f1)
in (match (uu____4428) with
| (c1, g_w) -> begin
(

let uu____4439 = (FStar_TypeChecker_Env.conj_guard g_c g_w)
in ((c1), (uu____4439)))
end))
end)
end))
end)))
in (

let uu____4440 = (weaken_flags lc.FStar_TypeChecker_Common.cflags)
in (FStar_TypeChecker_Common.mk_lcomp lc.FStar_TypeChecker_Common.eff_name lc.FStar_TypeChecker_Common.res_typ uu____4440 weaken))))


let strengthen_comp : FStar_TypeChecker_Env.env  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env reason c f flags -> (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
((c), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____4493 -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let pure_assert_wp = (

let uu____4497 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.pure_assert_wp_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____4497))
in (

let pure_assert_wp1 = (

let uu____4502 = (

let uu____4507 = (

let uu____4508 = (

let uu____4517 = (label_opt env reason r f)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____4517))
in (uu____4508)::[])
in (FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____4507))
in (uu____4502 FStar_Pervasives_Native.None r))
in (bind_pure_wp_with env pure_assert_wp1 c flags))))
end))


let strengthen_precondition : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_TypeChecker_Common.guard_t  ->  (FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t) = (fun reason env e_for_debugging_only lc g0 -> (

let uu____4587 = (FStar_TypeChecker_Env.is_trivial_guard_formula g0)
in (match (uu____4587) with
| true -> begin
((lc), (g0))
end
| uu____4594 -> begin
(

let flags = (

let uu____4599 = (

let uu____4607 = (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc)
in (match (uu____4607) with
| true -> begin
((true), ((FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]))
end
| uu____4621 -> begin
((false), ([]))
end))
in (match (uu____4599) with
| (maybe_trivial_post, flags) -> begin
(

let uu____4637 = (FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags (FStar_List.collect (fun uu___3_4645 -> (match (uu___3_4645) with
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
| uu____4648 -> begin
[]
end))))
in (FStar_List.append flags uu____4637))
end))
in (

let strengthen = (fun uu____4658 -> (

let uu____4659 = (FStar_TypeChecker_Common.lcomp_comp lc)
in (match (uu____4659) with
| (c, g_c) -> begin
(match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
((c), (g_c))
end
| uu____4675 -> begin
(

let g01 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (

let uu____4678 = (FStar_TypeChecker_Env.guard_form g01)
in (match (uu____4678) with
| FStar_TypeChecker_Common.Trivial -> begin
((c), (g_c))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____4685 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____4685) with
| true -> begin
(

let uu____4689 = (FStar_TypeChecker_Normalize.term_to_string env e_for_debugging_only)
in (

let uu____4691 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" uu____4689 uu____4691)))
end
| uu____4694 -> begin
()
end));
(

let uu____4696 = (strengthen_comp env reason c f flags)
in (match (uu____4696) with
| (c1, g_s) -> begin
(

let uu____4707 = (FStar_TypeChecker_Env.conj_guard g_c g_s)
in ((c1), (uu____4707)))
end));
)
end)))
end)
end)))
in (

let uu____4708 = (

let uu____4709 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_TypeChecker_Common.eff_name)
in (FStar_TypeChecker_Common.mk_lcomp uu____4709 lc.FStar_TypeChecker_Common.res_typ flags strengthen))
in ((uu____4708), ((

let uu___562_4711 = g0
in {FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Common.deferred = uu___562_4711.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___562_4711.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___562_4711.FStar_TypeChecker_Common.implicits}))))))
end)))


let lcomp_has_trivial_postcondition : FStar_TypeChecker_Common.lcomp  ->  Prims.bool = (fun lc -> ((FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) || (FStar_Util.for_some (fun uu___4_4720 -> (match (uu___4_4720) with
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
true
end
| uu____4724 -> begin
false
end)) lc.FStar_TypeChecker_Common.cflags)))


let maybe_add_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env uopt lc e -> (

let uu____4753 = ((FStar_TypeChecker_Common.is_lcomp_partial_return lc) || env.FStar_TypeChecker_Env.lax)
in (match (uu____4753) with
| true -> begin
e
end
| uu____4758 -> begin
(

let uu____4760 = ((lcomp_has_trivial_postcondition lc) && (

let uu____4763 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____4763)))
in (match (uu____4760) with
| true -> begin
(

let u = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
u
end
| FStar_Pervasives_Native.None -> begin
(env.FStar_TypeChecker_Env.universe_of env lc.FStar_TypeChecker_Common.res_typ)
end)
in (FStar_Syntax_Util.mk_with_type u lc.FStar_TypeChecker_Common.res_typ e))
end
| uu____4787 -> begin
e
end))
end)))


let maybe_capture_unit_refinement : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env t x c -> (

let t1 = (FStar_TypeChecker_Normalize.normalize_refinement FStar_TypeChecker_Normalize.whnf_steps env t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (b, phi) -> begin
(

let is_unit1 = (match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid)
end
| uu____4833 -> begin
false
end)
in (match (is_unit1) with
| true -> begin
(

let uu____4840 = (

let uu____4842 = (

let uu____4843 = (FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name)
in (FStar_All.pipe_right uu____4843 (FStar_TypeChecker_Env.norm_eff_name env)))
in (FStar_All.pipe_right uu____4842 (FStar_TypeChecker_Env.is_layered_effect env)))
in (match (uu____4840) with
| true -> begin
(

let uu____4852 = (FStar_Syntax_Subst.open_term ((((b), (FStar_Pervasives_Native.None)))::[]) phi)
in (match (uu____4852) with
| ((b1)::[], phi1) -> begin
(

let phi2 = (

let uu____4896 = (

let uu____4899 = (

let uu____4900 = (

let uu____4907 = (FStar_All.pipe_right b1 FStar_Pervasives_Native.fst)
in ((uu____4907), (FStar_Syntax_Syntax.unit_const)))
in FStar_Syntax_Syntax.NT (uu____4900))
in (uu____4899)::[])
in (FStar_Syntax_Subst.subst uu____4896 phi1))
in (weaken_comp env c phi2))
end))
end
| uu____4918 -> begin
(

let uu____4920 = (close_wp_comp env ((x)::[]) c)
in ((uu____4920), (FStar_TypeChecker_Env.trivial_guard)))
end))
end
| uu____4921 -> begin
((c), (FStar_TypeChecker_Env.trivial_guard))
end))
end
| uu____4923 -> begin
((c), (FStar_TypeChecker_Env.trivial_guard))
end)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Common.lcomp  ->  lcomp_with_binder  ->  FStar_TypeChecker_Common.lcomp = (fun r1 env e1opt lc1 uu____4951 -> (match (uu____4951) with
| (b, lc2) -> begin
(

let debug1 = (fun f -> (

let uu____4971 = ((FStar_TypeChecker_Env.debug env FStar_Options.Extreme) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("bind"))))
in (match (uu____4971) with
| true -> begin
(f ())
end
| uu____4976 -> begin
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

let uu____4984 = ((should_not_inline_lc lc11) || (should_not_inline_lc lc21))
in (match (uu____4984) with
| true -> begin
(FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]
end
| uu____4989 -> begin
(

let flags = (

let uu____4994 = (FStar_TypeChecker_Common.is_total_lcomp lc11)
in (match (uu____4994) with
| true -> begin
(

let uu____4999 = (FStar_TypeChecker_Common.is_total_lcomp lc21)
in (match (uu____4999) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____5004 -> begin
(

let uu____5006 = (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc21)
in (match (uu____5006) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5011 -> begin
[]
end))
end))
end
| uu____5013 -> begin
(

let uu____5015 = ((FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc11) && (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc21))
in (match (uu____5015) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____5020 -> begin
[]
end))
end))
in (

let uu____5022 = (lcomp_has_trivial_postcondition lc21)
in (match (uu____5022) with
| true -> begin
(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::flags
end
| uu____5027 -> begin
flags
end)))
end))
in (

let bind_it = (fun uu____5038 -> (

let uu____5039 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____5039) with
| true -> begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc21.FStar_TypeChecker_Common.res_typ)
in (

let uu____5047 = (lax_mk_tot_or_comp_l joined_eff u_t lc21.FStar_TypeChecker_Common.res_typ [])
in ((uu____5047), (FStar_TypeChecker_Env.trivial_guard))))
end
| uu____5048 -> begin
(

let uu____5050 = (FStar_TypeChecker_Common.lcomp_comp lc11)
in (match (uu____5050) with
| (c1, g_c1) -> begin
(

let uu____5061 = (FStar_TypeChecker_Common.lcomp_comp lc21)
in (match (uu____5061) with
| (c2, g_c2) -> begin
((debug1 (fun uu____5081 -> (

let uu____5082 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____5084 = (match (b) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (

let uu____5089 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n" uu____5082 uu____5084 uu____5089))))));
(

let aux = (fun uu____5107 -> (

let uu____5108 = (FStar_Syntax_Util.is_trivial_wp c1)
in (match (uu____5108) with
| true -> begin
(match (b) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl (((c2), ("trivial no binder")))
end
| FStar_Pervasives_Native.Some (uu____5139) -> begin
(

let uu____5140 = (FStar_Syntax_Util.is_ml_comp c2)
in (match (uu____5140) with
| true -> begin
FStar_Util.Inl (((c2), ("trivial ml")))
end
| uu____5161 -> begin
FStar_Util.Inr ("c1 trivial; but c2 is not ML")
end))
end)
end
| uu____5170 -> begin
(

let uu____5172 = ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2))
in (match (uu____5172) with
| true -> begin
FStar_Util.Inl (((c2), ("both ml")))
end
| uu____5193 -> begin
FStar_Util.Inr ("c1 not trivial, and both are not ML")
end))
end)))
in (

let try_simplify = (fun uu____5219 -> (

let aux_with_trivial_guard = (fun uu____5249 -> (

let uu____5250 = (aux ())
in (match (uu____5250) with
| FStar_Util.Inl (c, reason) -> begin
FStar_Util.Inl (((c), (FStar_TypeChecker_Env.trivial_guard), (reason)))
end
| FStar_Util.Inr (reason) -> begin
FStar_Util.Inr (reason)
end)))
in (

let uu____5308 = (

let uu____5310 = (FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Parser_Const.effect_GTot_lid)
in (FStar_Option.isNone uu____5310))
in (match (uu____5308) with
| true -> begin
(

let uu____5326 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____5326) with
| true -> begin
FStar_Util.Inl (((c2), (FStar_TypeChecker_Env.trivial_guard), ("Early in prims; we don\'t have bind yet")))
end
| uu____5351 -> begin
(

let uu____5353 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonTrivialPreConditionInPrims), ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")) uu____5353))
end))
end
| uu____5368 -> begin
(

let uu____5370 = (FStar_Syntax_Util.is_total_comp c1)
in (match (uu____5370) with
| true -> begin
(

let close1 = (fun x reason c -> (

let x1 = (

let uu___661_5416 = x
in {FStar_Syntax_Syntax.ppname = uu___661_5416.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___661_5416.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Syntax_Util.comp_result c1)})
in (

let uu____5417 = (maybe_capture_unit_refinement env x1.FStar_Syntax_Syntax.sort x1 c)
in (match (uu____5417) with
| (c3, g_c) -> begin
FStar_Util.Inl (((c3), (g_c), (reason)))
end))))
in (match (((e1opt), (b))) with
| (FStar_Pervasives_Native.Some (e), FStar_Pervasives_Native.Some (x)) -> begin
(

let uu____5475 = (FStar_All.pipe_right c2 (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[])))
in (FStar_All.pipe_right uu____5475 (close1 x "c1 Tot")))
end
| (uu____5491, FStar_Pervasives_Native.Some (x)) -> begin
(FStar_All.pipe_right c2 (close1 x "c1 Tot only close"))
end
| (uu____5516, uu____5517) -> begin
(aux_with_trivial_guard ())
end))
end
| uu____5530 -> begin
(

let uu____5532 = ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2))
in (match (uu____5532) with
| true -> begin
(

let uu____5547 = (

let uu____5555 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____5555), (FStar_TypeChecker_Env.trivial_guard), ("both GTot")))
in FStar_Util.Inl (uu____5547))
end
| uu____5566 -> begin
(aux_with_trivial_guard ())
end))
end))
end))))
in (

let uu____5568 = (try_simplify ())
in (match (uu____5568) with
| FStar_Util.Inl (c, g_c, reason) -> begin
((debug1 (fun uu____5603 -> (

let uu____5604 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "(2) bind: Simplified (because %s) to\n\t%s\n" reason uu____5604))));
(

let uu____5607 = (

let uu____5608 = (FStar_TypeChecker_Env.conj_guard g_c1 g_c2)
in (FStar_TypeChecker_Env.conj_guard g_c uu____5608))
in ((c), (uu____5607)));
)
end
| FStar_Util.Inr (reason) -> begin
((debug1 (fun uu____5622 -> (FStar_Util.print1 "(2) bind: Not simplified because %s\n" reason)));
(

let mk_bind1 = (fun c11 b1 c21 -> (

let uu____5648 = (mk_bind env c11 b1 c21 bind_flags r1)
in (match (uu____5648) with
| (c, g_bind) -> begin
(

let uu____5659 = (

let uu____5660 = (FStar_TypeChecker_Env.conj_guard g_c1 g_c2)
in (FStar_TypeChecker_Env.conj_guard uu____5660 g_bind))
in ((c), (uu____5659)))
end)))
in (

let mk_seq = (fun c11 b1 c21 -> (

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in (

let uu____5687 = (FStar_TypeChecker_Env.join env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____5687) with
| (m, uu____5699, lift2) -> begin
(

let uu____5701 = (lift_comp env c22 lift2)
in (match (uu____5701) with
| (c23, g2) -> begin
(

let uu____5712 = (destruct_wp_comp c12)
in (match (uu____5712) with
| (u1, t1, wp1) -> begin
(

let md_pure_or_ghost = (FStar_TypeChecker_Env.get_effect_decl env c12.FStar_Syntax_Syntax.effect_name)
in (

let trivial = (

let uu____5728 = (FStar_All.pipe_right md_pure_or_ghost FStar_Syntax_Util.get_wp_trivial_combinator)
in (FStar_All.pipe_right uu____5728 FStar_Util.must))
in (

let vc1 = (

let uu____5738 = (

let uu____5743 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u1)::[]) env md_pure_or_ghost trivial)
in (

let uu____5744 = (

let uu____5745 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____5754 = (

let uu____5765 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____5765)::[])
in (uu____5745)::uu____5754))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5743 uu____5744)))
in (uu____5738 FStar_Pervasives_Native.None r1))
in (

let uu____5798 = (strengthen_comp env FStar_Pervasives_Native.None c23 vc1 bind_flags)
in (match (uu____5798) with
| (c, g_s) -> begin
(

let uu____5813 = (FStar_TypeChecker_Env.conj_guards ((g_c1)::(g_c2)::(g2)::(g_s)::[]))
in ((c), (uu____5813)))
end)))))
end))
end))
end)))))
in (

let uu____5814 = (

let t = (FStar_Syntax_Util.comp_result c1)
in (match ((comp_univ_opt c1)) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5830 = (env.FStar_TypeChecker_Env.universe_of env t)
in ((uu____5830), (t)))
end
| FStar_Pervasives_Native.Some (u) -> begin
((u), (t))
end))
in (match (uu____5814) with
| (u_res_t1, res_t1) -> begin
(

let uu____5846 = ((FStar_Option.isSome b) && (should_return env e1opt lc11))
in (match (uu____5846) with
| true -> begin
(

let e1 = (FStar_Option.get e1opt)
in (

let x = (FStar_Option.get b)
in (

let uu____5855 = (FStar_Syntax_Util.is_partial_return c1)
in (match (uu____5855) with
| true -> begin
((debug1 (fun uu____5869 -> (

let uu____5870 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____5872 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case a): Substituting %s for %s" uu____5870 uu____5872)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (mk_bind1 c1 b c21));
)
end
| uu____5878 -> begin
(

let uu____5880 = (((FStar_Options.vcgen_optimize_bind_as_seq ()) && (lcomp_has_trivial_postcondition lc11)) && (

let uu____5883 = (FStar_TypeChecker_Env.try_lookup_lid env FStar_Parser_Const.with_type_lid)
in (FStar_Option.isSome uu____5883)))
in (match (uu____5880) with
| true -> begin
(

let e1' = (

let uu____5908 = (FStar_Options.vcgen_decorate_with_type ())
in (match (uu____5908) with
| true -> begin
(FStar_Syntax_Util.mk_with_type u_res_t1 res_t1 e1)
end
| uu____5911 -> begin
e1
end))
in ((debug1 (fun uu____5920 -> (

let uu____5921 = (FStar_TypeChecker_Normalize.term_to_string env e1')
in (

let uu____5923 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case b): Substituting %s for %s" uu____5921 uu____5923)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1'))))::[]) c2)
in (mk_seq c1 b c21));
))
end
| uu____5929 -> begin
((debug1 (fun uu____5938 -> (

let uu____5939 = (FStar_TypeChecker_Normalize.term_to_string env e1)
in (

let uu____5941 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print2 "(3) bind (case c): Adding equality %s = %s" uu____5939 uu____5941)))));
(

let c21 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e1))))::[]) c2)
in (

let x_eq_e = (

let uu____5948 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq2 u_res_t1 res_t1 e1 uu____5948))
in (

let uu____5949 = (

let uu____5954 = (

let uu____5955 = (

let uu____5956 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5956)::[])
in (FStar_TypeChecker_Env.push_binders env uu____5955))
in (weaken_comp uu____5954 c21 x_eq_e))
in (match (uu____5949) with
| (c22, g_w) -> begin
(

let uu____5981 = (mk_bind1 c1 b c22)
in (match (uu____5981) with
| (c, g_bind) -> begin
(

let uu____5992 = (FStar_TypeChecker_Env.conj_guard g_w g_bind)
in ((c), (uu____5992)))
end))
end))));
)
end))
end))))
end
| uu____5993 -> begin
(mk_bind1 c1 b c2)
end))
end))));
)
end))));
)
end))
end))
end)))
in (FStar_TypeChecker_Common.mk_lcomp joined_eff lc21.FStar_TypeChecker_Common.res_typ bind_flags bind_it)))))))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| uu____6009 -> begin
g2
end))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_TypeChecker_Common.lcomp = (fun env e lc -> (

let should_return1 = ((((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Env.lid_exists env FStar_Parser_Const.effect_GTot_lid)) && (should_return env (FStar_Pervasives_Native.Some (e)) lc)) && (

let uu____6033 = (FStar_TypeChecker_Common.is_lcomp_partial_return lc)
in (not (uu____6033))))
in (

let flags = (match (should_return1) with
| true -> begin
(

let uu____6041 = (FStar_TypeChecker_Common.is_total_lcomp lc)
in (match (uu____6041) with
| true -> begin
(FStar_Syntax_Syntax.RETURN)::lc.FStar_TypeChecker_Common.cflags
end
| uu____6046 -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_TypeChecker_Common.cflags
end))
end
| uu____6048 -> begin
lc.FStar_TypeChecker_Common.cflags
end)
in (

let refine1 = (fun uu____6059 -> (

let uu____6060 = (FStar_TypeChecker_Common.lcomp_comp lc)
in (match (uu____6060) with
| (c, g_c) -> begin
(

let u_t = (match ((comp_univ_opt c)) with
| FStar_Pervasives_Native.Some (u_t) -> begin
u_t
end
| FStar_Pervasives_Native.None -> begin
(env.FStar_TypeChecker_Env.universe_of env (FStar_Syntax_Util.comp_result c))
end)
in (

let uu____6073 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____6073) with
| true -> begin
(

let retc = (return_value env (FStar_Pervasives_Native.Some (u_t)) (FStar_Syntax_Util.comp_result c) e)
in (

let uu____6081 = (

let uu____6083 = (FStar_Syntax_Util.is_pure_comp c)
in (not (uu____6083)))
in (match (uu____6081) with
| true -> begin
(

let retc1 = (FStar_Syntax_Util.comp_to_comp_typ retc)
in (

let retc2 = (

let uu___780_6092 = retc1
in {FStar_Syntax_Syntax.comp_univs = uu___780_6092.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_GHOST_lid; FStar_Syntax_Syntax.result_typ = uu___780_6092.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___780_6092.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags})
in (

let uu____6093 = (FStar_Syntax_Syntax.mk_Comp retc2)
in ((uu____6093), (g_c)))))
end
| uu____6094 -> begin
(

let uu____6096 = (FStar_Syntax_Util.comp_set_flags retc flags)
in ((uu____6096), (g_c)))
end)))
end
| uu____6097 -> begin
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

let uu____6107 = (

let uu____6108 = (return_value env (FStar_Pervasives_Native.Some (u_t)) t xexp)
in (FStar_Syntax_Util.comp_set_flags uu____6108 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp uu____6107))
in (

let eq1 = (FStar_Syntax_Util.mk_eq2 u_t t xexp e)
in (

let eq_ret = (weaken_precondition env ret1 (FStar_TypeChecker_Common.NonTrivial (eq1)))
in (

let uu____6111 = (

let uu____6116 = (

let uu____6117 = (FStar_TypeChecker_Common.lcomp_of_comp c2)
in (bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None uu____6117 ((FStar_Pervasives_Native.Some (x)), (eq_ret))))
in (FStar_TypeChecker_Common.lcomp_comp uu____6116))
in (match (uu____6111) with
| (bind_c, g_bind) -> begin
(

let uu____6126 = (FStar_Syntax_Util.comp_set_flags bind_c flags)
in (

let uu____6127 = (FStar_TypeChecker_Env.conj_guard g_c g_bind)
in ((uu____6126), (uu____6127))))
end))))))))))
end)))
end)))
in (match ((not (should_return1))) with
| true -> begin
lc
end
| uu____6129 -> begin
(FStar_TypeChecker_Common.mk_lcomp lc.FStar_TypeChecker_Common.eff_name lc.FStar_TypeChecker_Common.res_typ flags refine1)
end)))))


let maybe_return_e2_and_bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_Syntax_Syntax.term  ->  lcomp_with_binder  ->  FStar_TypeChecker_Common.lcomp = (fun r env e1opt lc1 e2 uu____6163 -> (match (uu____6163) with
| (x, lc2) -> begin
(

let lc21 = (

let eff1 = (FStar_TypeChecker_Env.norm_eff_name env lc1.FStar_TypeChecker_Common.eff_name)
in (

let eff2 = (FStar_TypeChecker_Env.norm_eff_name env lc2.FStar_TypeChecker_Common.eff_name)
in (

let uu____6175 = (((

let uu____6179 = (is_pure_or_ghost_effect env eff1)
in (not (uu____6179))) || (should_not_inline_lc lc1)) && (is_pure_or_ghost_effect env eff2))
in (match (uu____6175) with
| true -> begin
(maybe_assume_result_eq_pure_term env e2 lc2)
end
| uu____6182 -> begin
lc2
end))))
in (bind r env e1opt lc1 ((x), (lc21))))
end))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (

let uu____6197 = (

let uu____6198 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid uu____6198))
in (FStar_Syntax_Syntax.fvar uu____6197 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)))


let mk_layered_conjunction : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env ed u_a a p ct1 ct2 r -> (

let uu____6248 = (

let uu____6253 = (

let uu____6254 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_layered_if_then_else_combinator)
in (FStar_All.pipe_right uu____6254 FStar_Util.must))
in (FStar_TypeChecker_Env.inst_tscheme_with uu____6253 ((u_a)::[])))
in (match (uu____6248) with
| (uu____6265, conjunction) -> begin
(

let uu____6267 = (

let uu____6276 = (FStar_List.map FStar_Pervasives_Native.fst ct1.FStar_Syntax_Syntax.effect_args)
in (

let uu____6291 = (FStar_List.map FStar_Pervasives_Native.fst ct2.FStar_Syntax_Syntax.effect_args)
in ((uu____6276), (uu____6291))))
in (match (uu____6267) with
| (is1, is2) -> begin
(

let conjunction_t_error = (fun s -> (

let uu____6337 = (

let uu____6339 = (FStar_Syntax_Print.term_to_string conjunction)
in (FStar_Util.format2 "conjunction %s does not have proper shape (reason:%s)" uu____6339 s))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____6337))))
in (

let uu____6343 = (

let uu____6388 = (

let uu____6389 = (FStar_Syntax_Subst.compress conjunction)
in uu____6389.FStar_Syntax_Syntax.n)
in (match (uu____6388) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____6438) when ((FStar_List.length bs) >= (Prims.parse_int "4")) -> begin
(

let uu____6470 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____6470) with
| ((a_b)::bs1, body1) -> begin
(

let uu____6542 = (FStar_List.splitAt ((FStar_List.length bs1) - (Prims.parse_int "3")) bs1)
in (match (uu____6542) with
| (rest_bs, (f_b)::(g_b)::(p_b)::[]) -> begin
(

let uu____6690 = (FStar_All.pipe_right body1 FStar_Syntax_Util.unascribe)
in ((a_b), (rest_bs), (f_b), (g_b), (p_b), (uu____6690)))
end))
end))
end
| uu____6723 -> begin
(

let uu____6724 = (conjunction_t_error "Either not an abstraction or not enough binders")
in (FStar_Errors.raise_error uu____6724 r))
end))
in (match (uu____6343) with
| (a_b, rest_bs, f_b, g_b, p_b, body) -> begin
(

let uu____6849 = (

let uu____6856 = (

let uu____6857 = (

let uu____6858 = (

let uu____6865 = (FStar_All.pipe_right a_b FStar_Pervasives_Native.fst)
in ((uu____6865), (a)))
in FStar_Syntax_Syntax.NT (uu____6858))
in (uu____6857)::[])
in (FStar_TypeChecker_Env.uvars_for_binders env rest_bs uu____6856 (fun b -> (

let uu____6881 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____6883 = (FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let uu____6885 = (FStar_All.pipe_right r FStar_Range.string_of_range)
in (FStar_Util.format3 "implicit var for binder %s of %s:conjunction at %s" uu____6881 uu____6883 uu____6885))))) r))
in (match (uu____6849) with
| (rest_bs_uvars, g_uvars) -> begin
(

let substs = (FStar_List.map2 (fun b t -> (

let uu____6923 = (

let uu____6930 = (FStar_All.pipe_right b FStar_Pervasives_Native.fst)
in ((uu____6930), (t)))
in FStar_Syntax_Syntax.NT (uu____6923))) ((a_b)::(FStar_List.append rest_bs ((p_b)::[]))) ((a)::(FStar_List.append rest_bs_uvars ((p)::[]))))
in (

let f_guard = (

let f_sort_is = (

let uu____6969 = (

let uu____6970 = (

let uu____6973 = (

let uu____6974 = (FStar_All.pipe_right f_b FStar_Pervasives_Native.fst)
in uu____6974.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Subst.compress uu____6973))
in uu____6970.FStar_Syntax_Syntax.n)
in (match (uu____6969) with
| FStar_Syntax_Syntax.Tm_app (uu____6985, (uu____6986)::is) -> begin
(

let uu____7028 = (FStar_All.pipe_right is (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7028 (FStar_List.map (FStar_Syntax_Subst.subst substs))))
end
| uu____7061 -> begin
(

let uu____7062 = (conjunction_t_error "f\'s type is not a repr type")
in (FStar_Errors.raise_error uu____7062 r))
end))
in (FStar_List.fold_left2 (fun g i1 f_i -> (

let uu____7078 = (FStar_TypeChecker_Rel.teq env i1 f_i)
in (FStar_TypeChecker_Env.conj_guard g uu____7078))) FStar_TypeChecker_Env.trivial_guard is1 f_sort_is))
in (

let g_guard = (

let g_sort_is = (

let uu____7083 = (

let uu____7084 = (

let uu____7087 = (

let uu____7088 = (FStar_All.pipe_right g_b FStar_Pervasives_Native.fst)
in uu____7088.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Subst.compress uu____7087))
in uu____7084.FStar_Syntax_Syntax.n)
in (match (uu____7083) with
| FStar_Syntax_Syntax.Tm_app (uu____7099, (uu____7100)::is) -> begin
(

let uu____7142 = (FStar_All.pipe_right is (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7142 (FStar_List.map (FStar_Syntax_Subst.subst substs))))
end
| uu____7175 -> begin
(

let uu____7176 = (conjunction_t_error "g\'s type is not a repr type")
in (FStar_Errors.raise_error uu____7176 r))
end))
in (FStar_List.fold_left2 (fun g i2 g_i -> (

let uu____7192 = (FStar_TypeChecker_Rel.teq env i2 g_i)
in (FStar_TypeChecker_Env.conj_guard g uu____7192))) FStar_TypeChecker_Env.trivial_guard is2 g_sort_is))
in (

let body1 = (FStar_Syntax_Subst.subst substs body)
in (

let is = (

let uu____7197 = (

let uu____7198 = (FStar_Syntax_Subst.compress body1)
in uu____7198.FStar_Syntax_Syntax.n)
in (match (uu____7197) with
| FStar_Syntax_Syntax.Tm_app (uu____7203, (a1)::args) -> begin
(FStar_List.map FStar_Pervasives_Native.fst args)
end
| uu____7258 -> begin
(

let uu____7259 = (conjunction_t_error "body is not a repr type")
in (FStar_Errors.raise_error uu____7259 r))
end))
in (

let uu____7268 = (

let uu____7269 = (

let uu____7270 = (FStar_All.pipe_right is (FStar_List.map FStar_Syntax_Syntax.as_arg))
in {FStar_Syntax_Syntax.comp_univs = (u_a)::[]; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = uu____7270; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____7269))
in (

let uu____7293 = (

let uu____7294 = (FStar_TypeChecker_Env.conj_guard g_uvars f_guard)
in (FStar_TypeChecker_Env.conj_guard uu____7294 g_guard))
in ((uu____7268), (uu____7293)))))))))
end))
end)))
end))
end)))


let mk_non_layered_conjunction : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env ed u_a a p ct1 ct2 uu____7339 -> (

let if_then_else1 = (

let uu____7345 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_wp_if_then_else_combinator)
in (FStar_All.pipe_right uu____7345 FStar_Util.must))
in (

let uu____7352 = (destruct_wp_comp ct1)
in (match (uu____7352) with
| (uu____7363, uu____7364, wp_t) -> begin
(

let uu____7366 = (destruct_wp_comp ct2)
in (match (uu____7366) with
| (uu____7377, uu____7378, wp_e) -> begin
(

let wp = (

let uu____7383 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (

let uu____7384 = (

let uu____7389 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_a)::[]) env ed if_then_else1)
in (

let uu____7390 = (

let uu____7391 = (FStar_Syntax_Syntax.as_arg a)
in (

let uu____7400 = (

let uu____7411 = (FStar_Syntax_Syntax.as_arg p)
in (

let uu____7420 = (

let uu____7431 = (FStar_Syntax_Syntax.as_arg wp_t)
in (

let uu____7440 = (

let uu____7451 = (FStar_Syntax_Syntax.as_arg wp_e)
in (uu____7451)::[])
in (uu____7431)::uu____7440))
in (uu____7411)::uu____7420))
in (uu____7391)::uu____7400))
in (FStar_Syntax_Syntax.mk_Tm_app uu____7389 uu____7390)))
in (uu____7384 FStar_Pervasives_Native.None uu____7383)))
in (

let uu____7500 = (mk_comp ed u_a a wp [])
in ((uu____7500), (FStar_TypeChecker_Env.trivial_guard))))
end))
end))))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list * (Prims.bool  ->  FStar_TypeChecker_Common.lcomp)) Prims.list  ->  FStar_TypeChecker_Common.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff uu____7570 -> (match (uu____7570) with
| (uu____7584, eff_label, uu____7586, uu____7587) -> begin
(join_effects env eff eff_label)
end)) FStar_Parser_Const.effect_PURE_lid lcases)
in (

let uu____7600 = (

let uu____7608 = (FStar_All.pipe_right lcases (FStar_Util.for_some (fun uu____7646 -> (match (uu____7646) with
| (uu____7661, uu____7662, flags, uu____7664) -> begin
(FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___5_7681 -> (match (uu___5_7681) with
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
true
end
| uu____7684 -> begin
false
end))))
end))))
in (match (uu____7608) with
| true -> begin
((true), ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
end
| uu____7698 -> begin
((false), ([]))
end))
in (match (uu____7600) with
| (should_not_inline_whole_match, bind_cases_flags) -> begin
(

let bind_cases = (fun uu____7721 -> (

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let uu____7723 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____7723) with
| true -> begin
(

let uu____7730 = (lax_mk_tot_or_comp_l eff u_res_t res_t [])
in ((uu____7730), (FStar_TypeChecker_Env.trivial_guard)))
end
| uu____7731 -> begin
(

let default_case = (

let post_k = (

let uu____7737 = (

let uu____7746 = (FStar_Syntax_Syntax.null_binder res_t)
in (uu____7746)::[])
in (

let uu____7765 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____7737 uu____7765)))
in (

let kwp = (

let uu____7771 = (

let uu____7780 = (FStar_Syntax_Syntax.null_binder post_k)
in (uu____7780)::[])
in (

let uu____7799 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____7771 uu____7799)))
in (

let post = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k)
in (

let wp = (

let uu____7806 = (

let uu____7807 = (FStar_Syntax_Syntax.mk_binder post)
in (uu____7807)::[])
in (

let uu____7826 = (

let uu____7829 = (

let uu____7836 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check uu____7836))
in (

let uu____7837 = (fvar_const env FStar_Parser_Const.false_lid)
in (FStar_All.pipe_left uu____7829 uu____7837)))
in (FStar_Syntax_Util.abs uu____7806 uu____7826 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Parser_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let maybe_return = (fun eff_label_then cthen -> (

let uu____7861 = (should_not_inline_whole_match || (

let uu____7864 = (is_pure_or_ghost_effect env eff)
in (not (uu____7864))))
in (match (uu____7861) with
| true -> begin
(cthen true)
end
| uu____7868 -> begin
(cthen false)
end)))
in (

let uu____7871 = (FStar_List.fold_right (fun uu____7924 uu____7925 -> (match (((uu____7924), (uu____7925))) with
| ((g, eff_label, uu____7979, cthen), (uu____7981, celse, g_comp)) -> begin
(

let uu____8022 = (

let uu____8027 = (maybe_return eff_label cthen)
in (FStar_TypeChecker_Common.lcomp_comp uu____8027))
in (match (uu____8022) with
| (cthen1, gthen) -> begin
(

let uu____8038 = (

let uu____8047 = (lift_comps env cthen1 celse FStar_Pervasives_Native.None false)
in (match (uu____8047) with
| (m, cthen2, celse1, g_lift) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let uu____8070 = (FStar_All.pipe_right cthen2 FStar_Syntax_Util.comp_to_comp_typ)
in (

let uu____8071 = (FStar_All.pipe_right celse1 FStar_Syntax_Util.comp_to_comp_typ)
in ((md), (uu____8070), (uu____8071), (g_lift)))))
end))
in (match (uu____8038) with
| (md, ct_then, ct_else, g_lift) -> begin
(

let fn = (

let uu____8121 = (FStar_All.pipe_right md FStar_Syntax_Util.is_layered)
in (match (uu____8121) with
| true -> begin
mk_layered_conjunction
end
| uu____8153 -> begin
mk_non_layered_conjunction
end))
in (

let uu____8155 = (

let uu____8160 = (FStar_TypeChecker_Env.get_range env)
in (fn env md u_res_t res_t g ct_then ct_else uu____8160))
in (match (uu____8155) with
| (c, g_conjunction) -> begin
(

let uu____8171 = (

let uu____8172 = (

let uu____8173 = (FStar_TypeChecker_Env.conj_guard g_comp gthen)
in (FStar_TypeChecker_Env.conj_guard uu____8173 g_lift))
in (FStar_TypeChecker_Env.conj_guard uu____8172 g_conjunction))
in ((FStar_Pervasives_Native.Some (md)), (c), (uu____8171)))
end)))
end))
end))
end)) lcases ((FStar_Pervasives_Native.None), (default_case), (FStar_TypeChecker_Env.trivial_guard)))
in (match (uu____7871) with
| (md, comp, g_comp) -> begin
(match (lcases) with
| [] -> begin
((comp), (g_comp))
end
| (uu____8207)::[] -> begin
((comp), (g_comp))
end
| uu____8250 -> begin
(

let uu____8267 = (

let uu____8269 = (FStar_All.pipe_right md FStar_Util.must)
in (FStar_All.pipe_right uu____8269 FStar_Syntax_Util.is_layered))
in (match (uu____8267) with
| true -> begin
((comp), (g_comp))
end
| uu____8278 -> begin
(

let comp1 = (FStar_TypeChecker_Env.comp_to_comp_typ env comp)
in (

let md1 = (FStar_TypeChecker_Env.get_effect_decl env comp1.FStar_Syntax_Syntax.effect_name)
in (

let uu____8282 = (destruct_wp_comp comp1)
in (match (uu____8282) with
| (uu____8293, uu____8294, wp) -> begin
(

let ite_wp = (

let uu____8297 = (FStar_All.pipe_right md1 FStar_Syntax_Util.get_wp_ite_combinator)
in (FStar_All.pipe_right uu____8297 FStar_Util.must))
in (

let wp1 = (

let uu____8307 = (

let uu____8312 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md1 ite_wp)
in (

let uu____8313 = (

let uu____8314 = (FStar_Syntax_Syntax.as_arg res_t)
in (

let uu____8323 = (

let uu____8334 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____8334)::[])
in (uu____8314)::uu____8323))
in (FStar_Syntax_Syntax.mk_Tm_app uu____8312 uu____8313)))
in (uu____8307 FStar_Pervasives_Native.None wp.FStar_Syntax_Syntax.pos))
in (

let uu____8367 = (mk_comp md1 u_res_t res_t wp1 bind_cases_flags)
in ((uu____8367), (g_comp)))))
end))))
end))
end)
end))))
end))))
in (FStar_TypeChecker_Common.mk_lcomp eff res_t bind_cases_flags bind_cases))
end))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun env e c c' -> (

let uu____8402 = (FStar_TypeChecker_Rel.sub_comp env c c')
in (match (uu____8402) with
| FStar_Pervasives_Native.None -> begin
(match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(

let uu____8418 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq env e c c')
in (

let uu____8424 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____8418 uu____8424)))
end
| uu____8431 -> begin
(

let uu____8433 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (

let uu____8439 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____8433 uu____8439)))
end)
end
| FStar_Pervasives_Native.Some (g) -> begin
((e), (c'), (g))
end)))


let universe_of_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe = (fun env u_res c -> (

let c_lid = (

let uu____8464 = (FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name)
in (FStar_All.pipe_right uu____8464 (FStar_TypeChecker_Env.norm_eff_name env)))
in (

let uu____8467 = (FStar_Syntax_Util.is_pure_or_ghost_effect c_lid)
in (match (uu____8467) with
| true -> begin
u_res
end
| uu____8470 -> begin
(

let is_total = (

let uu____8474 = (FStar_TypeChecker_Env.lookup_effect_quals env c_lid)
in (FStar_All.pipe_right uu____8474 (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.TotalEffect)))))
in (match ((not (is_total))) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____8483 -> begin
(

let uu____8485 = (FStar_TypeChecker_Env.effect_repr env c u_res)
in (match (uu____8485) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8488 = (

let uu____8494 = (

let uu____8496 = (FStar_Syntax_Print.lid_to_string c_lid)
in (FStar_Util.format1 "Effect %s is marked total but does not have a repr" uu____8496))
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____8494)))
in (FStar_Errors.raise_error uu____8488 c.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
end))
end))))


let check_trivial_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp_typ * FStar_Syntax_Syntax.formula * FStar_TypeChecker_Common.guard_t) = (fun env c -> (

let ct = (FStar_All.pipe_right c (FStar_TypeChecker_Env.unfold_effect_abbrev env))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____8520 = (destruct_wp_comp ct)
in (match (uu____8520) with
| (u_t, t, wp) -> begin
(

let vc = (

let uu____8539 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____8540 = (

let uu____8545 = (

let uu____8546 = (

let uu____8547 = (FStar_All.pipe_right md FStar_Syntax_Util.get_wp_trivial_combinator)
in (FStar_All.pipe_right uu____8547 FStar_Util.must))
in (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md uu____8546))
in (

let uu____8554 = (

let uu____8555 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____8564 = (

let uu____8575 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____8575)::[])
in (uu____8555)::uu____8564))
in (FStar_Syntax_Syntax.mk_Tm_app uu____8545 uu____8554)))
in (uu____8540 FStar_Pervasives_Native.None uu____8539)))
in (

let uu____8608 = (FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in ((ct), (vc), (uu____8608))))
end)))))


let coerce_with : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp) = (fun env e lc ty f us eargs mkcomp -> (

let uu____8663 = (FStar_TypeChecker_Env.try_lookup_lid env f)
in (match (uu____8663) with
| FStar_Pervasives_Native.Some (uu____8678) -> begin
((

let uu____8696 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Coercions")))
in (match (uu____8696) with
| true -> begin
(

let uu____8700 = (FStar_Ident.string_of_lid f)
in (FStar_Util.print1 "Coercing with %s!\n" uu____8700))
end
| uu____8703 -> begin
()
end));
(

let coercion = (

let uu____8706 = (FStar_Ident.set_lid_range f e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____8706 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let coercion1 = (FStar_Syntax_Syntax.mk_Tm_uinst coercion us)
in (

let coercion2 = (FStar_Syntax_Util.mk_app coercion1 eargs)
in (

let lc1 = (

let uu____8713 = (

let uu____8714 = (

let uu____8715 = (mkcomp ty)
in (FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp uu____8715))
in ((FStar_Pervasives_Native.None), (uu____8714)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) lc uu____8713))
in (

let e1 = (

let uu____8721 = (

let uu____8726 = (

let uu____8727 = (FStar_Syntax_Syntax.as_arg e)
in (uu____8727)::[])
in (FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____8726))
in (uu____8721 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in ((e1), (lc1)))))));
)
end
| FStar_Pervasives_Native.None -> begin
((

let uu____8761 = (

let uu____8767 = (

let uu____8769 = (FStar_Ident.string_of_lid f)
in (FStar_Util.format1 "Coercion %s was not found in the environment, not coercing." uu____8769))
in ((FStar_Errors.Warning_CoercionNotFound), (uu____8767)))
in (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos uu____8761));
((e), (lc));
)
end)))

type isErased =
| Yes of FStar_Syntax_Syntax.term
| Maybe
| No


let uu___is_Yes : isErased  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Yes (_0) -> begin
true
end
| uu____8788 -> begin
false
end))


let __proj__Yes__item___0 : isErased  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| Yes (_0) -> begin
_0
end))


let uu___is_Maybe : isErased  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____8806 -> begin
false
end))


let uu___is_No : isErased  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____8817 -> begin
false
end))


let rec check_erased : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  isErased = (fun env t -> (

let norm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.Iota)::[]))
in (

let t1 = (norm' env t)
in (

let t2 = (FStar_Syntax_Util.unrefine t1)
in (

let uu____8841 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____8841) with
| (h, args) -> begin
(

let h1 = (FStar_Syntax_Util.un_uinst h)
in (

let r = (

let uu____8886 = (

let uu____8901 = (

let uu____8902 = (FStar_Syntax_Subst.compress h1)
in uu____8902.FStar_Syntax_Syntax.n)
in ((uu____8901), (args)))
in (match (uu____8886) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid) -> begin
Yes (a)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8949), uu____8950) -> begin
Maybe
end
| (FStar_Syntax_Syntax.Tm_unknown, uu____8983) -> begin
Maybe
end
| (FStar_Syntax_Syntax.Tm_match (uu____9004, branches), uu____9006) -> begin
(FStar_All.pipe_right branches (FStar_List.fold_left (fun acc br -> (match (acc) with
| Yes (uu____9070) -> begin
Maybe
end
| Maybe -> begin
Maybe
end
| No -> begin
(

let uu____9071 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____9071) with
| (uu____9072, uu____9073, br_body) -> begin
(

let uu____9091 = (

let uu____9092 = (

let uu____9097 = (

let uu____9098 = (

let uu____9101 = (FStar_All.pipe_right br_body FStar_Syntax_Free.names)
in (FStar_All.pipe_right uu____9101 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____9098 (FStar_TypeChecker_Env.push_bvs env)))
in (check_erased uu____9097))
in (FStar_All.pipe_right br_body uu____9092))
in (match (uu____9091) with
| No -> begin
No
end
| uu____9112 -> begin
Maybe
end))
end))
end)) No))
end
| uu____9113 -> begin
No
end))
in r))
end))))))


let maybe_coerce_lc : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t) = (fun env e lc exp_t -> (

let should_coerce = ((((

let uu____9165 = (FStar_Options.use_two_phase_tc ())
in (not (uu____9165))) || env.FStar_TypeChecker_Env.phase1) || env.FStar_TypeChecker_Env.lax) || (FStar_Options.lax ()))
in (match ((not (should_coerce))) with
| true -> begin
((e), (lc), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____9174 -> begin
(

let is_t_term = (fun t -> (

let t1 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in (

let uu____9184 = (

let uu____9185 = (FStar_Syntax_Subst.compress t1)
in uu____9185.FStar_Syntax_Syntax.n)
in (match (uu____9184) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid)
end
| uu____9190 -> begin
false
end))))
in (

let is_t_term_view = (fun t -> (

let t1 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in (

let uu____9200 = (

let uu____9201 = (FStar_Syntax_Subst.compress t1)
in uu____9201.FStar_Syntax_Syntax.n)
in (match (uu____9200) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_view_lid)
end
| uu____9206 -> begin
false
end))))
in (

let is_type1 = (fun t -> (

let t1 = (FStar_TypeChecker_Normalize.unfold_whnf env t)
in (

let uu____9216 = (

let uu____9217 = (FStar_Syntax_Subst.compress t1)
in uu____9217.FStar_Syntax_Syntax.n)
in (match (uu____9216) with
| FStar_Syntax_Syntax.Tm_type (uu____9221) -> begin
true
end
| uu____9223 -> begin
false
end))))
in (

let res_typ = (FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ)
in (

let uu____9226 = (FStar_Syntax_Util.head_and_args res_typ)
in (match (uu____9226) with
| (head1, args) -> begin
((

let uu____9276 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Coercions")))
in (match (uu____9276) with
| true -> begin
(

let uu____9280 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____9282 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____9284 = (FStar_Syntax_Print.term_to_string res_typ)
in (

let uu____9286 = (FStar_Syntax_Print.term_to_string exp_t)
in (FStar_Util.print4 "(%s) Trying to coerce %s from type (%s) to type (%s)\n" uu____9280 uu____9282 uu____9284 uu____9286)))))
end
| uu____9289 -> begin
()
end));
(

let mk_erased = (fun u t -> (

let uu____9304 = (

let uu____9307 = (fvar_const env FStar_Parser_Const.erased_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____9307 ((u)::[])))
in (

let uu____9308 = (

let uu____9319 = (FStar_Syntax_Syntax.as_arg t)
in (uu____9319)::[])
in (FStar_Syntax_Util.mk_app uu____9304 uu____9308))))
in (

let uu____9344 = (

let uu____9359 = (

let uu____9360 = (FStar_Syntax_Util.un_uinst head1)
in uu____9360.FStar_Syntax_Syntax.n)
in ((uu____9359), (args)))
in (match (uu____9344) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) && (is_type1 exp_t)) -> begin
(

let uu____9398 = (coerce_with env e lc FStar_Syntax_Util.ktype0 FStar_Parser_Const.b2t_lid [] [] FStar_Syntax_Syntax.mk_Total)
in (match (uu____9398) with
| (e1, lc1) -> begin
((e1), (lc1), (FStar_TypeChecker_Env.trivial_guard))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid) && (is_t_term_view exp_t)) -> begin
(

let uu____9438 = (coerce_with env e lc FStar_Syntax_Syntax.t_term_view FStar_Parser_Const.inspect [] [] FStar_Syntax_Syntax.mk_Tac)
in (match (uu____9438) with
| (e1, lc1) -> begin
((e1), (lc1), (FStar_TypeChecker_Env.trivial_guard))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_view_lid) && (is_t_term exp_t)) -> begin
(

let uu____9478 = (coerce_with env e lc FStar_Syntax_Syntax.t_term FStar_Parser_Const.pack [] [] FStar_Syntax_Syntax.mk_Tac)
in (match (uu____9478) with
| (e1, lc1) -> begin
((e1), (lc1), (FStar_TypeChecker_Env.trivial_guard))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.binder_lid) && (is_t_term exp_t)) -> begin
(

let uu____9518 = (coerce_with env e lc FStar_Syntax_Syntax.t_term FStar_Parser_Const.binder_to_term [] [] FStar_Syntax_Syntax.mk_Tac)
in (match (uu____9518) with
| (e1, lc1) -> begin
((e1), (lc1), (FStar_TypeChecker_Env.trivial_guard))
end))
end
| uu____9539 -> begin
(

let uu____9554 = (

let uu____9559 = (check_erased env res_typ)
in (

let uu____9560 = (check_erased env exp_t)
in ((uu____9559), (uu____9560))))
in (match (uu____9554) with
| (No, Yes (ty)) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env ty)
in (

let uu____9569 = (FStar_TypeChecker_Rel.get_subtyping_predicate env res_typ ty)
in (match (uu____9569) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (g) -> begin
(

let g1 = (FStar_TypeChecker_Env.apply_guard g e)
in (

let uu____9580 = (

let uu____9585 = (

let uu____9586 = (FStar_Syntax_Syntax.iarg ty)
in (uu____9586)::[])
in (coerce_with env e lc exp_t FStar_Parser_Const.hide ((u)::[]) uu____9585 FStar_Syntax_Syntax.mk_Total))
in (match (uu____9580) with
| (e1, lc1) -> begin
((e1), (lc1), (g1))
end)))
end)))
end
| (Yes (ty), No) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env ty)
in (

let uu____9621 = (

let uu____9626 = (

let uu____9627 = (FStar_Syntax_Syntax.iarg ty)
in (uu____9627)::[])
in (coerce_with env e lc ty FStar_Parser_Const.reveal ((u)::[]) uu____9626 FStar_Syntax_Syntax.mk_GTotal))
in (match (uu____9621) with
| (e1, lc1) -> begin
((e1), (lc1), (FStar_TypeChecker_Env.trivial_guard))
end)))
end
| uu____9660 -> begin
((e), (lc), (FStar_TypeChecker_Env.trivial_guard))
end))
end)));
)
end))))))
end)))


let coerce_views : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp) FStar_Pervasives_Native.option = (fun env e lc -> (

let rt = lc.FStar_TypeChecker_Common.res_typ
in (

let rt1 = (FStar_Syntax_Util.unrefine rt)
in (

let uu____9695 = (FStar_Syntax_Util.head_and_args rt1)
in (match (uu____9695) with
| (hd1, args) -> begin
(

let uu____9744 = (

let uu____9759 = (

let uu____9760 = (FStar_Syntax_Subst.compress hd1)
in uu____9760.FStar_Syntax_Syntax.n)
in ((uu____9759), (args)))
in (match (uu____9744) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid) -> begin
(

let uu____9798 = (coerce_with env e lc FStar_Syntax_Syntax.t_term_view FStar_Parser_Const.inspect [] [] FStar_Syntax_Syntax.mk_Tac)
in (FStar_All.pipe_left (fun _9825 -> FStar_Pervasives_Native.Some (_9825)) uu____9798))
end
| uu____9826 -> begin
FStar_Pervasives_Native.None
end))
end)))))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t) = (fun env e lc t -> ((

let uu____9879 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____9879) with
| true -> begin
(

let uu____9882 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____9884 = (FStar_TypeChecker_Common.lcomp_to_string lc)
in (

let uu____9886 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n" uu____9882 uu____9884 uu____9886))))
end
| uu____9889 -> begin
()
end));
(

let use_eq = (env.FStar_TypeChecker_Env.use_eq || (

let uu____9896 = (FStar_TypeChecker_Env.effect_decl_opt env lc.FStar_TypeChecker_Common.eff_name)
in (match (uu____9896) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
end
| uu____9921 -> begin
false
end)))
in (

let gopt = (match (use_eq) with
| true -> begin
(

let uu____9947 = (FStar_TypeChecker_Rel.try_teq true env lc.FStar_TypeChecker_Common.res_typ t)
in ((uu____9947), (false)))
end
| uu____9955 -> begin
(

let uu____9957 = (FStar_TypeChecker_Rel.get_subtyping_predicate env lc.FStar_TypeChecker_Common.res_typ t)
in ((uu____9957), (true)))
end)
in (match (gopt) with
| (FStar_Pervasives_Native.None, uu____9970) -> begin
(match (env.FStar_TypeChecker_Env.failhard) with
| true -> begin
(

let uu____9982 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t lc.FStar_TypeChecker_Common.res_typ)
in (FStar_Errors.raise_error uu____9982 e.FStar_Syntax_Syntax.pos))
end
| uu____9994 -> begin
((FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_TypeChecker_Common.res_typ t);
((e), ((

let uu___1200_9998 = lc
in {FStar_TypeChecker_Common.eff_name = uu___1200_9998.FStar_TypeChecker_Common.eff_name; FStar_TypeChecker_Common.res_typ = t; FStar_TypeChecker_Common.cflags = uu___1200_9998.FStar_TypeChecker_Common.cflags; FStar_TypeChecker_Common.comp_thunk = uu___1200_9998.FStar_TypeChecker_Common.comp_thunk})), (FStar_TypeChecker_Env.trivial_guard));
)
end)
end
| (FStar_Pervasives_Native.Some (g), apply_guard1) -> begin
(

let uu____10005 = (FStar_TypeChecker_Env.guard_form g)
in (match (uu____10005) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let strengthen_trivial = (fun uu____10021 -> (

let uu____10022 = (FStar_TypeChecker_Common.lcomp_comp lc)
in (match (uu____10022) with
| (c, g_c) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let set_result_typ1 = (fun c1 -> (FStar_Syntax_Util.set_result_typ c1 t))
in (

let uu____10042 = (

let uu____10044 = (FStar_Syntax_Util.eq_tm t res_t)
in (Prims.op_Equality uu____10044 FStar_Syntax_Util.Equal))
in (match (uu____10042) with
| true -> begin
((

let uu____10051 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____10051) with
| true -> begin
(

let uu____10055 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____10057 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n" uu____10055 uu____10057)))
end
| uu____10060 -> begin
()
end));
(

let uu____10062 = (set_result_typ1 c)
in ((uu____10062), (g_c)));
)
end
| uu____10063 -> begin
(

let is_res_t_refinement = (

let res_t1 = (FStar_TypeChecker_Normalize.normalize_refinement FStar_TypeChecker_Normalize.whnf_steps env res_t)
in (match (res_t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (uu____10069) -> begin
true
end
| uu____10077 -> begin
false
end))
in (match (is_res_t_refinement) with
| true -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (res_t.FStar_Syntax_Syntax.pos)) res_t)
in (

let cret = (

let uu____10086 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env (comp_univ_opt c) res_t uu____10086))
in (

let lc1 = (

let uu____10088 = (FStar_TypeChecker_Common.lcomp_of_comp c)
in (

let uu____10089 = (

let uu____10090 = (FStar_TypeChecker_Common.lcomp_of_comp cret)
in ((FStar_Pervasives_Native.Some (x)), (uu____10090)))
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____10088 uu____10089)))
in ((

let uu____10094 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____10094) with
| true -> begin
(

let uu____10098 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____10100 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____10102 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____10104 = (FStar_TypeChecker_Common.lcomp_to_string lc1)
in (FStar_Util.print4 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n" uu____10098 uu____10100 uu____10102 uu____10104)))))
end
| uu____10107 -> begin
()
end));
(

let uu____10109 = (FStar_TypeChecker_Common.lcomp_comp lc1)
in (match (uu____10109) with
| (c1, g_lc) -> begin
(

let uu____10120 = (set_result_typ1 c1)
in (

let uu____10121 = (FStar_TypeChecker_Env.conj_guard g_c g_lc)
in ((uu____10120), (uu____10121))))
end));
))))
end
| uu____10122 -> begin
((

let uu____10125 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____10125) with
| true -> begin
(

let uu____10129 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____10131 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n" uu____10129 uu____10131)))
end
| uu____10134 -> begin
()
end));
(

let uu____10136 = (set_result_typ1 c)
in ((uu____10136), (g_c)));
)
end))
end))))
end)))
in (

let lc1 = (FStar_TypeChecker_Common.mk_lcomp lc.FStar_TypeChecker_Common.eff_name t lc.FStar_TypeChecker_Common.cflags strengthen_trivial)
in ((e), (lc1), (g))))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g1 = (

let uu___1237_10140 = g
in {FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Common.deferred = uu___1237_10140.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___1237_10140.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___1237_10140.FStar_TypeChecker_Common.implicits})
in (

let strengthen = (fun uu____10150 -> (

let uu____10151 = (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))
in (match (uu____10151) with
| true -> begin
(FStar_TypeChecker_Common.lcomp_comp lc)
end
| uu____10158 -> begin
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::[]) env f)
in (

let uu____10161 = (

let uu____10162 = (FStar_Syntax_Subst.compress f1)
in uu____10162.FStar_Syntax_Syntax.n)
in (match (uu____10161) with
| FStar_Syntax_Syntax.Tm_abs (uu____10169, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____10171; FStar_Syntax_Syntax.vars = uu____10172}, uu____10173) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(

let lc1 = (

let uu___1253_10199 = lc
in {FStar_TypeChecker_Common.eff_name = uu___1253_10199.FStar_TypeChecker_Common.eff_name; FStar_TypeChecker_Common.res_typ = t; FStar_TypeChecker_Common.cflags = uu___1253_10199.FStar_TypeChecker_Common.cflags; FStar_TypeChecker_Common.comp_thunk = uu___1253_10199.FStar_TypeChecker_Common.comp_thunk})
in (FStar_TypeChecker_Common.lcomp_comp lc1))
end
| uu____10200 -> begin
(

let uu____10201 = (FStar_TypeChecker_Common.lcomp_comp lc)
in (match (uu____10201) with
| (c, g_c) -> begin
((

let uu____10213 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____10213) with
| true -> begin
(

let uu____10217 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_TypeChecker_Common.res_typ)
in (

let uu____10219 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____10221 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (

let uu____10223 = (FStar_TypeChecker_Normalize.term_to_string env f1)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" uu____10217 uu____10219 uu____10221 uu____10223)))))
end
| uu____10226 -> begin
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

let uu____10236 = (

let uu____10241 = (

let uu____10242 = (FStar_Syntax_Syntax.as_arg xexp)
in (uu____10242)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____10241))
in (uu____10236 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
end
| uu____10267 -> begin
f1
end)
in (

let uu____10269 = (

let uu____10274 = (FStar_All.pipe_left (fun _10295 -> FStar_Pervasives_Native.Some (_10295)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_TypeChecker_Common.res_typ t))
in (

let uu____10296 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let uu____10297 = (FStar_TypeChecker_Common.lcomp_of_comp cret)
in (

let uu____10298 = (FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition uu____10274 uu____10296 e uu____10297 uu____10298)))))
in (match (uu____10269) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x1 = (

let uu___1271_10306 = x
in {FStar_Syntax_Syntax.ppname = uu___1271_10306.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1271_10306.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_TypeChecker_Common.res_typ})
in (

let c1 = (

let uu____10308 = (FStar_TypeChecker_Common.lcomp_of_comp c)
in (bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) uu____10308 ((FStar_Pervasives_Native.Some (x1)), (eq_ret))))
in (

let uu____10311 = (FStar_TypeChecker_Common.lcomp_comp c1)
in (match (uu____10311) with
| (c2, g_lc) -> begin
((

let uu____10323 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____10323) with
| true -> begin
(

let uu____10327 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (FStar_Util.print1 "Strengthened to %s\n" uu____10327))
end
| uu____10330 -> begin
()
end));
(

let uu____10332 = (FStar_TypeChecker_Env.conj_guard g_c g_lc)
in ((c2), (uu____10332)));
)
end))))
end)))))));
)
end))
end)))
end)))
in (

let flags = (FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags (FStar_List.collect (fun uu___6_10341 -> (match (uu___6_10341) with
| FStar_Syntax_Syntax.RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| uu____10344 -> begin
[]
end))))
in (

let lc1 = (

let uu____10346 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_TypeChecker_Common.eff_name)
in (FStar_TypeChecker_Common.mk_lcomp uu____10346 t flags strengthen))
in (

let g2 = (

let uu___1287_10348 = g1
in {FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Common.deferred = uu___1287_10348.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___1287_10348.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___1287_10348.FStar_TypeChecker_Common.implicits})
in ((e), (lc1), (g2)))))))
end))
end)));
))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t)
in (

let uu____10384 = (

let uu____10387 = (

let uu____10392 = (

let uu____10393 = (

let uu____10402 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____10402))
in (uu____10393)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens uu____10392))
in (uu____10387 FStar_Pervasives_Native.None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x uu____10384))))
in (

let norm1 = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env t))
in (

let uu____10425 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____10425) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp)))
end
| uu____10436 -> begin
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (uu____10444) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Total (uu____10460) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____10477 = ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Ghost_lid))
in (match (uu____10477) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, uu____10493))::((ens, uu____10495))::uu____10496 -> begin
(

let uu____10539 = (

let uu____10542 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____10542))
in (

let uu____10543 = (

let uu____10544 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm1 uu____10544))
in ((uu____10539), (uu____10543))))
end
| uu____10547 -> begin
(

let uu____10558 = (

let uu____10564 = (

let uu____10566 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" uu____10566))
in ((FStar_Errors.Fatal_EffectConstructorNotFullyApplied), (uu____10564)))
in (FStar_Errors.raise_error uu____10558 comp.FStar_Syntax_Syntax.pos))
end)
end
| uu____10576 -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env comp)
in (match (ct1.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____10586))::uu____10587 -> begin
(

let uu____10614 = (

let uu____10619 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_requires)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10619))
in (match (uu____10614) with
| (us_r, uu____10651) -> begin
(

let uu____10652 = (

let uu____10657 = (FStar_TypeChecker_Env.lookup_lid env FStar_Parser_Const.as_ensures)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10657))
in (match (uu____10652) with
| (us_e, uu____10689) -> begin
(

let r = ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (

let uu____10692 = (

let uu____10693 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar uu____10693 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____10692 us_r))
in (

let as_ens = (

let uu____10695 = (

let uu____10696 = (FStar_Ident.set_lid_range FStar_Parser_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar uu____10696 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____10695 us_e))
in (

let req = (

let uu____10700 = (

let uu____10705 = (

let uu____10706 = (

let uu____10717 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____10717)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____10706)
in (FStar_Syntax_Syntax.mk_Tm_app as_req uu____10705))
in (uu____10700 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (

let uu____10757 = (

let uu____10762 = (

let uu____10763 = (

let uu____10774 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____10774)::[])
in (((ct1.FStar_Syntax_Syntax.result_typ), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::uu____10763)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens uu____10762))
in (uu____10757 FStar_Pervasives_Native.None ct1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____10811 = (

let uu____10814 = (norm1 req)
in FStar_Pervasives_Native.Some (uu____10814))
in (

let uu____10815 = (

let uu____10816 = (mk_post_type ct1.FStar_Syntax_Syntax.result_typ ens)
in (norm1 uu____10816))
in ((uu____10811), (uu____10815)))))))))
end))
end))
end
| uu____10819 -> begin
(failwith "Impossible")
end))
end))
end)
end)))))


let reify_body : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.steps  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env steps t -> (

let tm = (FStar_Syntax_Util.mk_reify t)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize (FStar_List.append ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) steps) env tm)
in ((

let uu____10858 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____10858) with
| true -> begin
(

let uu____10863 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____10865 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____10863 uu____10865)))
end
| uu____10868 -> begin
()
end));
tm';
))))


let reify_body_with_arg : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.steps  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.term = (fun env steps head1 arg -> (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((arg)::[])))) FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize (FStar_List.append ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) steps) env tm)
in ((

let uu____10924 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____10924) with
| true -> begin
(

let uu____10929 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____10931 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "Reified body %s \nto %s\n" uu____10929 uu____10931)))
end
| uu____10934 -> begin
()
end));
tm';
))))


let remove_reify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____10942 = (

let uu____10944 = (

let uu____10945 = (FStar_Syntax_Subst.compress t)
in uu____10945.FStar_Syntax_Syntax.n)
in (match (uu____10944) with
| FStar_Syntax_Syntax.Tm_app (uu____10949) -> begin
false
end
| uu____10967 -> begin
true
end))
in (match (uu____10942) with
| true -> begin
t
end
| uu____10970 -> begin
(

let uu____10972 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____10972) with
| (head1, args) -> begin
(

let uu____11015 = (

let uu____11017 = (

let uu____11018 = (FStar_Syntax_Subst.compress head1)
in uu____11018.FStar_Syntax_Syntax.n)
in (match (uu____11017) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____11023 -> begin
false
end))
in (match (uu____11015) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(FStar_Pervasives_Native.fst x)
end
| uu____11055 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____11067 -> begin
t
end))
end))
end)))


let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Common.guard_t) = (fun env e t -> (

let torig = (FStar_Syntax_Subst.compress t)
in (match ((not (env.FStar_TypeChecker_Env.instantiate_imp))) with
| true -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____11099 -> begin
((

let uu____11102 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____11102) with
| true -> begin
(

let uu____11105 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11107 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____11109 = (

let uu____11111 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Common.string_of_option FStar_Syntax_Print.term_to_string uu____11111))
in (FStar_Util.print3 "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n" uu____11105 uu____11107 uu____11109))))
end
| uu____11115 -> begin
()
end));
(

let number_of_implicits = (fun t1 -> (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env t1)
in (

let uu____11124 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____11124) with
| (formals, uu____11140) -> begin
(

let n_implicits = (

let uu____11162 = (FStar_All.pipe_right formals (FStar_Util.prefix_until (fun uu____11240 -> (match (uu____11240) with
| (uu____11248, imp) -> begin
((FStar_Option.isNone imp) || (

let uu____11255 = (FStar_Syntax_Util.eq_aqual imp (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)))
in (Prims.op_Equality uu____11255 FStar_Syntax_Util.Equal)))
end))))
in (match (uu____11162) with
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

let uu____11380 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____11380) with
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

let uu____11394 = (

let uu____11400 = (

let uu____11402 = (FStar_Util.string_of_int n_expected)
in (

let uu____11404 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11406 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" uu____11402 uu____11404 uu____11406))))
in ((FStar_Errors.Fatal_MissingImplicitArguments), (uu____11400)))
in (

let uu____11410 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____11394 uu____11410)))
end
| uu____11414 -> begin
FStar_Pervasives_Native.Some ((n_available - n_expected))
end)))
end)))
in (

let decr_inst = (fun uu___7_11428 -> (match (uu___7_11428) with
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

let uu____11471 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____11471) with
| (bs1, c1) -> begin
(

let rec aux = (fun subst1 inst_n bs2 -> (match (((inst_n), (bs2))) with
| (FStar_Pervasives_Native.Some (_11602), uu____11589) when (_11602 = (Prims.parse_int "0")) -> begin
(([]), (bs2), (subst1), (FStar_TypeChecker_Env.trivial_guard))
end
| (uu____11635, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11637))))::rest) -> begin
(

let t2 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____11671 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t2)
in (match (uu____11671) with
| (v1, uu____11712, g) -> begin
((

let uu____11727 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____11727) with
| true -> begin
(

let uu____11730 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.print1 "maybe_instantiate: Instantiating implicit with %s\n" uu____11730))
end
| uu____11733 -> begin
()
end));
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____11740 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____11740) with
| (args, bs3, subst3, g') -> begin
(

let uu____11833 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::args), (bs3), (subst3), (uu____11833)))
end)));
)
end)))
end
| (uu____11860, ((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau))))::rest) -> begin
(

let t2 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____11897 = (

let uu____11910 = (

let uu____11917 = (

let uu____11922 = (FStar_Dyn.mkdyn env)
in ((uu____11922), (tau)))
in FStar_Pervasives_Native.Some (uu____11917))
in (FStar_TypeChecker_Env.new_implicit_var_aux "Instantiation of meta argument" e.FStar_Syntax_Syntax.pos env t2 FStar_Syntax_Syntax.Strict uu____11910))
in (match (uu____11897) with
| (v1, uu____11955, g) -> begin
((

let uu____11970 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____11970) with
| true -> begin
(

let uu____11973 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.print1 "maybe_instantiate: Instantiating meta argument with %s\n" uu____11973))
end
| uu____11976 -> begin
()
end));
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (v1))))::subst1
in (

let uu____11983 = (aux subst2 (decr_inst inst_n) rest)
in (match (uu____11983) with
| (args, bs3, subst3, g') -> begin
(

let uu____12076 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((v1), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::args), (bs3), (subst3), (uu____12076)))
end)));
)
end)))
end
| (uu____12103, bs3) -> begin
(([]), (bs3), (subst1), (FStar_TypeChecker_Env.trivial_guard))
end))
in (

let uu____12151 = (

let uu____12178 = (inst_n_binders t1)
in (aux [] uu____12178 bs1))
in (match (uu____12151) with
| (args, bs2, subst1, guard) -> begin
(match (((args), (bs2))) with
| ([], uu____12250) -> begin
((e), (torig), (guard))
end
| (uu____12281, []) when (

let uu____12312 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____12312))) -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____12314 -> begin
(

let t2 = (match (bs2) with
| [] -> begin
(FStar_Syntax_Util.comp_result c1)
end
| uu____12342 -> begin
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
| uu____12355 -> begin
((e), (torig), (FStar_TypeChecker_Env.trivial_guard))
end)))));
)
end)))


let string_of_univs : FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  Prims.string = (fun univs1 -> (

let uu____12367 = (

let uu____12371 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____12371 (FStar_List.map (fun u -> (

let uu____12383 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____12383 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right uu____12367 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> (

let uu____12411 = (FStar_Util.set_is_empty x)
in (match (uu____12411) with
| true -> begin
[]
end
| uu____12416 -> begin
(

let s = (

let uu____12429 = (

let uu____12432 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x uu____12432))
in (FStar_All.pipe_right uu____12429 FStar_Util.set_elements))
in ((

let uu____12448 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____12448) with
| true -> begin
(

let uu____12453 = (

let uu____12455 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs uu____12455))
in (FStar_Util.print1 "univ_vars in env: %s\n" uu____12453))
end
| uu____12459 -> begin
()
end));
(

let r = (

let uu____12464 = (FStar_TypeChecker_Env.get_range env)
in FStar_Pervasives_Native.Some (uu____12464))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in ((

let uu____12503 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____12503) with
| true -> begin
(

let uu____12508 = (

let uu____12510 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____12510))
in (

let uu____12514 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (

let uu____12516 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" uu____12508 uu____12514 uu____12516))))
end
| uu____12519 -> begin
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

let uu____12546 = (FStar_Util.set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right uu____12546 FStar_Util.set_elements))
in univnames1))))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], uu____12585) -> begin
generalized_univ_names
end
| (uu____12592, []) -> begin
explicit_univ_names
end
| uu____12599 -> begin
(

let uu____12608 = (

let uu____12614 = (

let uu____12616 = (FStar_Syntax_Print.term_to_string t)
in (Prims.op_Hat "Generalized universe in a term containing explicit universe annotation : " uu____12616))
in ((FStar_Errors.Fatal_UnexpectedGeneralizedUniverse), (uu____12614)))
in (FStar_Errors.raise_error uu____12608 t.FStar_Syntax_Syntax.pos))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env t0)
in (

let univnames1 = (gather_free_univnames env t)
in ((

let uu____12638 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____12638) with
| true -> begin
(

let uu____12643 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____12645 = (FStar_Syntax_Print.univ_names_to_string univnames1)
in (FStar_Util.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" uu____12643 uu____12645)))
end
| uu____12648 -> begin
()
end));
(

let univs1 = (FStar_Syntax_Free.univs t)
in ((

let uu____12654 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____12654) with
| true -> begin
(

let uu____12659 = (string_of_univs univs1)
in (FStar_Util.print1 "univs to gen : %s\n" uu____12659))
end
| uu____12662 -> begin
()
end));
(

let gen1 = (gen_univs env univs1)
in ((

let uu____12668 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____12668) with
| true -> begin
(

let uu____12673 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____12675 = (FStar_Syntax_Print.univ_names_to_string gen1)
in (FStar_Util.print2 "After generalization, t: %s and univs: %s\n" uu____12673 uu____12675)))
end
| uu____12678 -> begin
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

let uu____12759 = (

let uu____12761 = (FStar_Util.for_all (fun uu____12775 -> (match (uu____12775) with
| (uu____12785, uu____12786, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) lecs)
in (FStar_All.pipe_left Prims.op_Negation uu____12761))
in (match (uu____12759) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12829 -> begin
(

let norm1 = (fun c -> ((

let uu____12838 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____12838) with
| true -> begin
(

let uu____12841 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" uu____12841))
end
| uu____12844 -> begin
()
end));
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env c)
in ((

let uu____12848 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____12848) with
| true -> begin
(

let uu____12851 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" uu____12851))
end
| uu____12854 -> begin
()
end));
c1;
));
))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (

let uu____12869 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right uu____12869 FStar_Util.set_elements)))
in (

let univs_and_uvars_of_lec = (fun uu____12903 -> (match (uu____12903) with
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

let uu____12940 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____12940) with
| true -> begin
(

let uu____12945 = (

let uu____12947 = (

let uu____12951 = (FStar_Util.set_elements univs1)
in (FStar_All.pipe_right uu____12951 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____12947 (FStar_String.concat ", ")))
in (

let uu____12999 = (

let uu____13001 = (

let uu____13005 = (FStar_Util.set_elements uvt)
in (FStar_All.pipe_right uu____13005 (FStar_List.map (fun u -> (

let uu____13018 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____13020 = (FStar_Syntax_Print.term_to_string u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____13018 uu____13020)))))))
in (FStar_All.pipe_right uu____13001 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____12945 uu____12999)))
end
| uu____13029 -> begin
()
end));
(

let univs2 = (

let uu____13034 = (FStar_Util.set_elements uvt)
in (FStar_List.fold_left (fun univs2 uv -> (

let uu____13046 = (FStar_Syntax_Free.univs uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.set_union univs2 uu____13046))) univs1 uu____13034))
in (

let uvs = (gen_uvars uvt)
in ((

let uu____13053 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen")))
in (match (uu____13053) with
| true -> begin
(

let uu____13058 = (

let uu____13060 = (

let uu____13064 = (FStar_Util.set_elements univs2)
in (FStar_All.pipe_right uu____13064 (FStar_List.map (fun u -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))))))
in (FStar_All.pipe_right uu____13060 (FStar_String.concat ", ")))
in (

let uu____13112 = (

let uu____13114 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> (

let uu____13128 = (FStar_Syntax_Print.uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____13130 = (FStar_TypeChecker_Normalize.term_to_string env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format2 "(%s : %s)" uu____13128 uu____13130))))))
in (FStar_All.pipe_right uu____13114 (FStar_String.concat ", ")))
in (FStar_Util.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____13058 uu____13112)))
end
| uu____13139 -> begin
()
end));
((univs2), (uvs), (((lbname), (e), (c1))));
)));
)))))
end))
in (

let uu____13151 = (

let uu____13168 = (FStar_List.hd lecs)
in (univs_and_uvars_of_lec uu____13168))
in (match (uu____13151) with
| (univs1, uvs, lec_hd) -> begin
(

let force_univs_eq = (fun lec2 u1 u2 -> (

let uu____13258 = ((FStar_Util.set_is_subset_of u1 u2) && (FStar_Util.set_is_subset_of u2 u1))
in (match (uu____13258) with
| true -> begin
()
end
| uu____13261 -> begin
(

let uu____13263 = lec_hd
in (match (uu____13263) with
| (lb1, uu____13271, uu____13272) -> begin
(

let uu____13273 = lec2
in (match (uu____13273) with
| (lb2, uu____13281, uu____13282) -> begin
(

let msg = (

let uu____13285 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____13287 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s" uu____13285 uu____13287)))
in (

let uu____13290 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleSetOfUniverse), (msg)) uu____13290)))
end))
end))
end)))
in (

let force_uvars_eq = (fun lec2 u1 u2 -> (

let uvars_subseteq = (fun u11 u21 -> (FStar_All.pipe_right u11 (FStar_Util.for_all (fun u -> (FStar_All.pipe_right u21 (FStar_Util.for_some (fun u' -> (FStar_Syntax_Unionfind.equiv u.FStar_Syntax_Syntax.ctx_uvar_head u'.FStar_Syntax_Syntax.ctx_uvar_head))))))))
in (

let uu____13358 = ((uvars_subseteq u1 u2) && (uvars_subseteq u2 u1))
in (match (uu____13358) with
| true -> begin
()
end
| uu____13361 -> begin
(

let uu____13363 = lec_hd
in (match (uu____13363) with
| (lb1, uu____13371, uu____13372) -> begin
(

let uu____13373 = lec2
in (match (uu____13373) with
| (lb2, uu____13381, uu____13382) -> begin
(

let msg = (

let uu____13385 = (FStar_Syntax_Print.lbname_to_string lb1)
in (

let uu____13387 = (FStar_Syntax_Print.lbname_to_string lb2)
in (FStar_Util.format2 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s" uu____13385 uu____13387)))
in (

let uu____13390 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_IncompatibleNumberOfTypes), (msg)) uu____13390)))
end))
end))
end))))
in (

let lecs1 = (

let uu____13401 = (FStar_List.tl lecs)
in (FStar_List.fold_right (fun this_lec lecs1 -> (

let uu____13454 = (univs_and_uvars_of_lec this_lec)
in (match (uu____13454) with
| (this_univs, this_uvs, this_lec1) -> begin
((force_univs_eq this_lec1 univs1 this_univs);
(force_uvars_eq this_lec1 uvs this_uvs);
(this_lec1)::lecs1;
)
end))) uu____13401 []))
in (

let lecs2 = (lec_hd)::lecs1
in (

let gen_types = (fun uvs1 -> (

let fail1 = (fun k -> (

let uu____13559 = lec_hd
in (match (uu____13559) with
| (lbname, e, c) -> begin
(

let uu____13569 = (

let uu____13575 = (

let uu____13577 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____13579 = (FStar_Syntax_Print.lbname_to_string lbname)
in (

let uu____13581 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' in the type of %s (%s)" uu____13577 uu____13579 uu____13581))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____13575)))
in (

let uu____13585 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____13569 uu____13585)))
end)))
in (FStar_All.pipe_right uvs1 (FStar_List.map (fun u -> (

let uu____13604 = (FStar_Syntax_Unionfind.find u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____13604) with
| FStar_Pervasives_Native.Some (uu____13613) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| uu____13621 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____13625 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____13625) with
| (bs, kres) -> begin
((

let uu____13669 = (

let uu____13670 = (

let uu____13673 = (FStar_TypeChecker_Normalize.unfold_whnf env kres)
in (FStar_Syntax_Util.unrefine uu____13673))
in uu____13670.FStar_Syntax_Syntax.n)
in (match (uu____13669) with
| FStar_Syntax_Syntax.Tm_type (uu____13674) -> begin
(

let free = (FStar_Syntax_Free.names kres)
in (

let uu____13678 = (

let uu____13680 = (FStar_Util.set_is_empty free)
in (not (uu____13680)))
in (match (uu____13678) with
| true -> begin
(fail1 kres)
end
| uu____13683 -> begin
()
end)))
end
| uu____13685 -> begin
(fail1 kres)
end));
(

let a = (

let uu____13687 = (

let uu____13690 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _13693 -> FStar_Pervasives_Native.Some (_13693)) uu____13690))
in (FStar_Syntax_Syntax.new_bv uu____13687 kres))
in (

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Syntax.bv_to_name a)
end
| uu____13701 -> begin
(

let uu____13710 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Util.abs bs uu____13710 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot kres)))))
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

let ecs = (FStar_All.pipe_right lecs2 (FStar_List.map (fun uu____13813 -> (match (uu____13813) with
| (lbname, e, c) -> begin
(

let uu____13859 = (match (((gen_tvars), (gen_univs1))) with
| ([], []) -> begin
((e), (c), ([]))
end
| uu____13920 -> begin
(

let uu____13933 = ((e), (c))
in (match (uu____13933) with
| (e0, c0) -> begin
(

let c1 = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env c)
in (

let e1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env e)
in (

let e2 = (match (is_rec) with
| true -> begin
(

let tvar_args = (FStar_List.map (fun uu____13973 -> (match (uu____13973) with
| (x, uu____13979) -> begin
(

let uu____13980 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.iarg uu____13980))
end)) gen_tvars)
in (

let instantiate_lbname_with_app = (fun tm fv -> (

let uu____13998 = (

let uu____14000 = (FStar_Util.right lbname)
in (FStar_Syntax_Syntax.fv_eq fv uu____14000))
in (match (uu____13998) with
| true -> begin
(FStar_Syntax_Syntax.mk_Tm_app tm tvar_args FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end
| uu____14004 -> begin
tm
end)))
in (FStar_Syntax_InstFV.inst instantiate_lbname_with_app e1)))
end
| uu____14006 -> begin
e1
end)
in (

let t = (

let uu____14009 = (

let uu____14010 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c1))
in uu____14010.FStar_Syntax_Syntax.n)
in (match (uu____14009) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let uu____14035 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (uu____14035) with
| (bs1, cod1) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append gen_tvars bs1) cod1)
end))
end
| uu____14046 -> begin
(FStar_Syntax_Util.arrow gen_tvars c1)
end))
in (

let e' = (FStar_Syntax_Util.abs gen_tvars e2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1))))
in (

let uu____14050 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (uu____14050), (gen_tvars))))))))
end))
end)
in (match (uu____13859) with
| (e1, c1, gvs) -> begin
((lbname), (gen_univs1), (e1), (c1), (gvs))
end))
end))))
in FStar_Pervasives_Native.Some (ecs)))))))))
end))))))
end)))


let generalize : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.binder Prims.list) Prims.list = (fun env is_rec lecs -> ((

let uu____14197 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____14197) with
| true -> begin
(

let uu____14200 = (

let uu____14202 = (FStar_List.map (fun uu____14217 -> (match (uu____14217) with
| (lb, uu____14226, uu____14227) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right uu____14202 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" uu____14200))
end
| uu____14234 -> begin
()
end));
(

let univnames_lecs = (FStar_List.map (fun uu____14253 -> (match (uu____14253) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (

let uu____14282 = (gen env is_rec lecs)
in (match (uu____14282) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun uu____14381 -> (match (uu____14381) with
| (l, t, c) -> begin
((l), ([]), (t), (c), ([]))
end))))
end
| FStar_Pervasives_Native.Some (luecs) -> begin
((

let uu____14443 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____14443) with
| true -> begin
(FStar_All.pipe_right luecs (FStar_List.iter (fun uu____14491 -> (match (uu____14491) with
| (l, us, e, c, gvs) -> begin
(

let uu____14525 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____14527 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____14529 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (

let uu____14531 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____14533 = (FStar_Syntax_Print.binders_to_string ", " gvs)
in (FStar_Util.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n" uu____14525 uu____14527 uu____14529 uu____14531 uu____14533))))))
end))))
end
| uu____14537 -> begin
()
end));
luecs;
)
end))
in (FStar_List.map2 (fun univnames1 uu____14578 -> (match (uu____14578) with
| (l, generalized_univs, t, c, gvs) -> begin
(

let uu____14622 = (check_universe_generalization univnames1 generalized_univs t)
in ((l), (uu____14622), (t), (c), (gvs)))
end)) univnames_lecs generalized_lecs)));
))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t) = (fun env e lc t2 -> (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check1 = (fun env2 t1 t21 -> (match (env2.FStar_TypeChecker_Env.use_eq) with
| true -> begin
(FStar_TypeChecker_Rel.try_teq true env2 t1 t21)
end
| uu____14685 -> begin
(

let uu____14687 = (FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21)
in (match (uu____14687) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____14693 = (FStar_TypeChecker_Env.apply_guard f e)
in (FStar_All.pipe_left (fun _14696 -> FStar_Pervasives_Native.Some (_14696)) uu____14693))
end))
end))
in (

let decorate = (fun e1 t -> (

let e2 = (FStar_Syntax_Subst.compress e1)
in (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let uu___1740_14716 = x
in {FStar_Syntax_Syntax.ppname = uu___1740_14716.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1740_14716.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end
| uu____14717 -> begin
e2
end)))
in (

let uu____14718 = (maybe_coerce_lc env1 e lc t2)
in (match (uu____14718) with
| (e1, lc1, g_c) -> begin
(

let uu____14734 = (check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2)
in (match (uu____14734) with
| FStar_Pervasives_Native.None -> begin
(

let uu____14743 = (FStar_TypeChecker_Err.expected_expression_of_type env1 t2 e1 lc1.FStar_TypeChecker_Common.res_typ)
in (

let uu____14749 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____14743 uu____14749)))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____14758 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____14758) with
| true -> begin
(

let uu____14763 = (FStar_TypeChecker_Rel.guard_to_string env1 g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") uu____14763))
end
| uu____14767 -> begin
()
end));
(

let uu____14769 = (decorate e1 t2)
in (

let uu____14770 = (FStar_TypeChecker_Env.conj_guard g g_c)
in ((uu____14769), (lc1), (uu____14770))));
)
end))
end))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> ((

let uu____14798 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____14798) with
| true -> begin
(

let uu____14801 = (FStar_TypeChecker_Common.lcomp_to_string lc)
in (FStar_Util.print1 "check_top_level, lc = %s\n" uu____14801))
end
| uu____14804 -> begin
()
end));
(

let discharge = (fun g1 -> ((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(FStar_TypeChecker_Common.is_pure_lcomp lc);
))
in (

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let uu____14815 = (FStar_TypeChecker_Common.lcomp_comp lc)
in (match (uu____14815) with
| (c, g_c) -> begin
(

let uu____14827 = (FStar_TypeChecker_Common.is_total_lcomp lc)
in (match (uu____14827) with
| true -> begin
(

let uu____14835 = (

let uu____14837 = (FStar_TypeChecker_Env.conj_guard g1 g_c)
in (discharge uu____14837))
in ((uu____14835), (c)))
end
| uu____14839 -> begin
(

let steps = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]
in (

let c1 = (

let uu____14845 = (

let uu____14846 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____14846 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right uu____14845 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (

let uu____14847 = (check_trivial_precondition env c1)
in (match (uu____14847) with
| (ct, vc, g_pre) -> begin
((

let uu____14863 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____14863) with
| true -> begin
(

let uu____14868 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" uu____14868))
end
| uu____14871 -> begin
()
end));
(

let uu____14873 = (

let uu____14875 = (

let uu____14876 = (FStar_TypeChecker_Env.conj_guard g_c g_pre)
in (FStar_TypeChecker_Env.conj_guard g1 uu____14876))
in (discharge uu____14875))
in (

let uu____14877 = (FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp)
in ((uu____14873), (uu____14877))));
)
end))))
end))
end))));
))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head1 seen_args -> (

let short_bin_op = (fun f uu___8_14911 -> (match (uu___8_14911) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst1, uu____14921))::[] -> begin
(f fst1)
end
| uu____14946 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (

let uu____14958 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right uu____14958 (fun _14959 -> FStar_TypeChecker_Common.NonTrivial (_14959)))))
in (

let op_or_e = (fun e -> (

let uu____14970 = (

let uu____14971 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg uu____14971))
in (FStar_All.pipe_right uu____14970 (fun _14974 -> FStar_TypeChecker_Common.NonTrivial (_14974)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _14981 -> FStar_TypeChecker_Common.NonTrivial (_14981))))
in (

let op_or_t = (fun t -> (

let uu____14992 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right uu____14992 (fun _14995 -> FStar_TypeChecker_Common.NonTrivial (_14995)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _15002 -> FStar_TypeChecker_Common.NonTrivial (_15002))))
in (

let short_op_ite = (fun uu___9_15008 -> (match (uu___9_15008) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, uu____15018))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, uu____15045))::[] -> begin
(

let uu____15086 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right uu____15086 (fun _15087 -> FStar_TypeChecker_Common.NonTrivial (_15087))))
end
| uu____15088 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (

let uu____15100 = (

let uu____15108 = (short_bin_op op_and_e)
in ((FStar_Parser_Const.op_And), (uu____15108)))
in (

let uu____15116 = (

let uu____15126 = (

let uu____15134 = (short_bin_op op_or_e)
in ((FStar_Parser_Const.op_Or), (uu____15134)))
in (

let uu____15142 = (

let uu____15152 = (

let uu____15160 = (short_bin_op op_and_t)
in ((FStar_Parser_Const.and_lid), (uu____15160)))
in (

let uu____15168 = (

let uu____15178 = (

let uu____15186 = (short_bin_op op_or_t)
in ((FStar_Parser_Const.or_lid), (uu____15186)))
in (

let uu____15194 = (

let uu____15204 = (

let uu____15212 = (short_bin_op op_imp_t)
in ((FStar_Parser_Const.imp_lid), (uu____15212)))
in (uu____15204)::(((FStar_Parser_Const.ite_lid), (short_op_ite)))::[])
in (uu____15178)::uu____15194))
in (uu____15152)::uu____15168))
in (uu____15126)::uu____15142))
in (uu____15100)::uu____15116))
in (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____15274 = (FStar_Util.find_map table (fun uu____15289 -> (match (uu____15289) with
| (x, mk1) -> begin
(

let uu____15306 = (FStar_Ident.lid_equals x lid)
in (match (uu____15306) with
| true -> begin
(

let uu____15311 = (mk1 seen_args)
in FStar_Pervasives_Native.Some (uu____15311))
end
| uu____15312 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (uu____15274) with
| FStar_Pervasives_Native.None -> begin
FStar_TypeChecker_Common.Trivial
end
| FStar_Pervasives_Native.Some (g) -> begin
g
end)))
end
| uu____15315 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (

let uu____15323 = (

let uu____15324 = (FStar_Syntax_Util.un_uinst l)
in uu____15324.FStar_Syntax_Syntax.n)
in (match (uu____15323) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.imp_lid)::(FStar_Parser_Const.ite_lid)::[]))
end
| uu____15329 -> begin
false
end)))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs1 -> (match (bs1) with
| ((hd1, uu____15365))::uu____15366 -> begin
(FStar_Syntax_Syntax.range_of_bv hd1)
end
| uu____15385 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((uu____15394, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____15395))))::uu____15396 -> begin
bs
end
| uu____15414 -> begin
(

let uu____15415 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____15415) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____15419 = (

let uu____15420 = (FStar_Syntax_Subst.compress t)
in uu____15420.FStar_Syntax_Syntax.n)
in (match (uu____15419) with
| FStar_Syntax_Syntax.Tm_arrow (bs', uu____15424) -> begin
(

let uu____15445 = (FStar_Util.prefix_until (fun uu___10_15485 -> (match (uu___10_15485) with
| (uu____15493, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____15494))) -> begin
false
end
| uu____15499 -> begin
true
end)) bs')
in (match (uu____15445) with
| FStar_Pervasives_Native.None -> begin
bs
end
| FStar_Pervasives_Native.Some ([], uu____15535, uu____15536) -> begin
bs
end
| FStar_Pervasives_Native.Some (imps, uu____15608, uu____15609) -> begin
(

let uu____15682 = (FStar_All.pipe_right imps (FStar_Util.for_all (fun uu____15702 -> (match (uu____15702) with
| (x, uu____15711) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end))))
in (match (uu____15682) with
| true -> begin
(

let r = (pos bs)
in (

let imps1 = (FStar_All.pipe_right imps (FStar_List.map (fun uu____15760 -> (match (uu____15760) with
| (x, i) -> begin
(

let uu____15779 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((uu____15779), (i)))
end))))
in (FStar_List.append imps1 bs)))
end
| uu____15788 -> begin
bs
end))
end))
end
| uu____15790 -> begin
bs
end))
end))
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 t -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in (

let uu____15819 = (((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1)))
in (match (uu____15819) with
| true -> begin
e
end
| uu____15822 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end)))))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in (

let uu____15850 = (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid))
in (match (uu____15850) with
| true -> begin
e
end
| uu____15853 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end))))


let d : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> ((

let uu____15893 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____15893) with
| true -> begin
((

let uu____15898 = (FStar_Ident.text_of_lid lident)
in (d uu____15898));
(

let uu____15900 = (FStar_Ident.text_of_lid lident)
in (

let uu____15902 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" uu____15900 uu____15902)));
)
end
| uu____15905 -> begin
()
end));
(

let fv = (

let uu____15908 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident uu____15908 FStar_Pervasives_Native.None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (((FStar_Syntax_Util.mk_letbinding lbname [] FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def [] FStar_Range.dummyRange))::[]))
in (

let sig_ctx = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_let (((lb), ((lident)::[])))))
in (

let uu____15920 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (((

let uu___1901_15922 = sig_ctx
in {FStar_Syntax_Syntax.sigel = uu___1901_15922.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___1901_15922.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]; FStar_Syntax_Syntax.sigmeta = uu___1901_15922.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1901_15922.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___1901_15922.FStar_Syntax_Syntax.sigopts})), (uu____15920)))))));
))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (

let visibility = (fun uu___11_15940 -> (match (uu___11_15940) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____15943 -> begin
false
end))
in (

let reducibility = (fun uu___12_15951 -> (match (uu___12_15951) with
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
| uu____15958 -> begin
false
end))
in (

let assumption = (fun uu___13_15966 -> (match (uu___13_15966) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.New -> begin
true
end
| uu____15970 -> begin
false
end))
in (

let reification = (fun uu___14_15978 -> (match (uu___14_15978) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____15981) -> begin
true
end
| uu____15983 -> begin
false
end))
in (

let inferred = (fun uu___15_15991 -> (match (uu___15_15991) with
| FStar_Syntax_Syntax.Discriminator (uu____15993) -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____15995) -> begin
true
end
| FStar_Syntax_Syntax.RecordType (uu____16001) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____16011) -> begin
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
| uu____16024 -> begin
false
end))
in (

let has_eq = (fun uu___16_16032 -> (match (uu___16_16032) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____16036 -> begin
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
| FStar_Syntax_Syntax.Reflectable (uu____16115) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((reification x) || (inferred x)) || (visibility x)) || (Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect)) || (Prims.op_Equality x FStar_Syntax_Syntax.Visible_default)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____16122 -> begin
true
end))
in (

let check_erasable = (fun quals se1 r -> (

let lids = (FStar_Syntax_Util.lids_of_sigelt se1)
in (

let val_exists = (FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____16155 = (FStar_TypeChecker_Env.try_lookup_val_decl env l)
in (FStar_Option.isSome uu____16155)))))
in (

let val_has_erasable_attr = (FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let attrs_opt = (FStar_TypeChecker_Env.lookup_attrs_of_lid env l)
in ((FStar_Option.isSome attrs_opt) && (

let uu____16186 = (FStar_Option.get attrs_opt)
in (FStar_Syntax_Util.has_attribute uu____16186 FStar_Parser_Const.erasable_attr)))))))
in (

let se_has_erasable_attr = (FStar_Syntax_Util.has_attribute se1.FStar_Syntax_Syntax.sigattrs FStar_Parser_Const.erasable_attr)
in ((match (((val_exists && val_has_erasable_attr) && (not (se_has_erasable_attr)))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_QulifierListNotPermitted), ("Mismatch of attributes between declaration and definition: Declaration is marked `erasable` but the definition is not")) r)
end
| uu____16197 -> begin
()
end);
(match (((val_exists && (not (val_has_erasable_attr))) && se_has_erasable_attr)) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_QulifierListNotPermitted), ("Mismatch of attributed between declaration and definition: Definition is marked `erasable` but the declaration is not")) r)
end
| uu____16203 -> begin
()
end);
(match (se_has_erasable_attr) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (uu____16206) -> begin
(

let uu____16215 = (

let uu____16217 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___17_16223 -> (match (uu___17_16223) with
| FStar_Syntax_Syntax.Noeq -> begin
true
end
| uu____16226 -> begin
false
end))))
in (not (uu____16217)))
in (match (uu____16215) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_QulifierListNotPermitted), ("Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")) r)
end
| uu____16231 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____16233) -> begin
()
end
| uu____16240 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_QulifierListNotPermitted), ("Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions")) r)
end)
end
| uu____16243 -> begin
()
end);
))))))
in (

let quals = (FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se) (FStar_List.filter (fun x -> (not ((Prims.op_Equality x FStar_Syntax_Syntax.Logic))))))
in (

let uu____16254 = (

let uu____16256 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___18_16262 -> (match (uu___18_16262) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____16265 -> begin
false
end))))
in (FStar_All.pipe_right uu____16256 Prims.op_Negation))
in (match (uu____16254) with
| true -> begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) quals)
in (

let err' = (fun msg -> (

let uu____16286 = (

let uu____16292 = (

let uu____16294 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" uu____16294 msg))
in ((FStar_Errors.Fatal_QulifierListNotPermitted), (uu____16292)))
in (FStar_Errors.raise_error uu____16286 r)))
in (

let err = (fun msg -> (err' (Prims.op_Hat ": " msg)))
in (

let err'1 = (fun uu____16312 -> (err' ""))
in ((match ((Prims.op_disEquality (FStar_List.length quals) (FStar_List.length no_dup_quals))) with
| true -> begin
(err "duplicate qualifiers")
end
| uu____16317 -> begin
()
end);
(

let uu____16320 = (

let uu____16322 = (FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals)))
in (not (uu____16322)))
in (match (uu____16320) with
| true -> begin
(err "ill-formed combination")
end
| uu____16329 -> begin
()
end));
(check_erasable quals se r);
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, uu____16333), uu____16334) -> begin
((

let uu____16346 = (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
in (match (uu____16346) with
| true -> begin
(err "recursive definitions cannot be marked inline")
end
| uu____16353 -> begin
()
end));
(

let uu____16355 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x)))))
in (match (uu____16355) with
| true -> begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end
| uu____16364 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_bundle (uu____16366) -> begin
((

let uu____16376 = (

let uu____16378 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((((Prims.op_Equality x FStar_Syntax_Syntax.Abstract) || (Prims.op_Equality x FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality x FStar_Syntax_Syntax.NoExtract)) || (inferred x)) || (visibility x)) || (has_eq x)))))
in (not (uu____16378)))
in (match (uu____16376) with
| true -> begin
(err'1 ())
end
| uu____16386 -> begin
()
end));
(

let uu____16388 = ((FStar_All.pipe_right quals (FStar_List.existsb (fun uu___19_16394 -> (match (uu___19_16394) with
| FStar_Syntax_Syntax.Unopteq -> begin
true
end
| uu____16397 -> begin
false
end)))) && (FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs FStar_Parser_Const.erasable_attr))
in (match (uu____16388) with
| true -> begin
(err "unopteq is not allowed on an erasable inductives since they don\'t have decidable equality")
end
| uu____16401 -> begin
()
end));
)
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____16403) -> begin
(

let uu____16410 = (FStar_All.pipe_right quals (FStar_Util.for_some has_eq))
in (match (uu____16410) with
| true -> begin
(err'1 ())
end
| uu____16416 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____16418) -> begin
(

let uu____16425 = (

let uu____16427 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (Prims.op_Equality x FStar_Syntax_Syntax.Assumption)))))
in (not (uu____16427)))
in (match (uu____16425) with
| true -> begin
(err'1 ())
end
| uu____16435 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____16437) -> begin
(

let uu____16438 = (

let uu____16440 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((Prims.op_Equality x FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x)))))
in (not (uu____16440)))
in (match (uu____16438) with
| true -> begin
(err'1 ())
end
| uu____16448 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____16450) -> begin
(

let uu____16463 = (

let uu____16465 = (FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x)))))
in (not (uu____16465)))
in (match (uu____16463) with
| true -> begin
(err'1 ())
end
| uu____16473 -> begin
()
end))
end
| uu____16475 -> begin
()
end);
))))))
end
| uu____16476 -> begin
()
end))))))))))))


let must_erase_for_extraction : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun g t -> (

let rec descend = (fun env t1 -> (

let uu____16514 = (

let uu____16515 = (FStar_Syntax_Subst.compress t1)
in uu____16515.FStar_Syntax_Syntax.n)
in (match (uu____16514) with
| FStar_Syntax_Syntax.Tm_arrow (uu____16519) -> begin
(

let uu____16534 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____16534) with
| (bs, c) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in ((FStar_Syntax_Util.is_ghost_effect (FStar_Syntax_Util.comp_effect_name c)) || ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (aux env1 (FStar_Syntax_Util.comp_result c)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____16567; FStar_Syntax_Syntax.index = uu____16568; FStar_Syntax_Syntax.sort = t2}, uu____16570) -> begin
(aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____16579) -> begin
(descend env head1)
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____16605) -> begin
(descend env head1)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_TypeChecker_Env.fv_has_attr env fv FStar_Parser_Const.must_erase_for_extraction_attr)
end
| uu____16611 -> begin
false
end)))
and aux = (fun env t1 -> (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Unascribe)::[]) env t1)
in (

let res = ((FStar_TypeChecker_Env.non_informative env t2) || (descend env t2))
in ((

let uu____16621 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Extraction")))
in (match (uu____16621) with
| true -> begin
(

let uu____16626 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "must_erase=%s: %s\n" (match (res) with
| true -> begin
"true"
end
| uu____16632 -> begin
"false"
end) uu____16626))
end
| uu____16635 -> begin
()
end));
res;
))))
in (aux g t)))


let fresh_effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t) = (fun env r eff_name signature_ts repr_ts_opt u a_tm -> (

let fail1 = (fun t -> (

let uu____16691 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env eff_name t)
in (FStar_Errors.raise_error uu____16691 r)))
in (

let uu____16701 = (FStar_TypeChecker_Env.inst_tscheme signature_ts)
in (match (uu____16701) with
| (uu____16710, signature) -> begin
(

let uu____16712 = (

let uu____16713 = (FStar_Syntax_Subst.compress signature)
in uu____16713.FStar_Syntax_Syntax.n)
in (match (uu____16712) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____16721) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| (a)::bs2 -> begin
(

let uu____16769 = (FStar_TypeChecker_Env.uvars_for_binders env bs2 ((FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst a)), (a_tm))))::[]) (fun b -> (

let uu____16784 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____16786 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "uvar for binder %s when creating a fresh repr for %s at %s" uu____16784 eff_name.FStar_Ident.str uu____16786)))) r)
in (match (uu____16769) with
| (is, g) -> begin
(

let uu____16799 = (match (repr_ts_opt) with
| FStar_Pervasives_Native.None -> begin
(

let eff_c = (

let uu____16801 = (

let uu____16802 = (FStar_List.map FStar_Syntax_Syntax.as_arg is)
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = eff_name; FStar_Syntax_Syntax.result_typ = a_tm; FStar_Syntax_Syntax.effect_args = uu____16802; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____16801))
in (

let uu____16821 = (

let uu____16828 = (

let uu____16829 = (

let uu____16844 = (

let uu____16853 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_unit)
in (uu____16853)::[])
in ((uu____16844), (eff_c)))
in FStar_Syntax_Syntax.Tm_arrow (uu____16829))
in (FStar_Syntax_Syntax.mk uu____16828))
in (uu____16821 FStar_Pervasives_Native.None r)))
end
| FStar_Pervasives_Native.Some (repr_ts) -> begin
(

let repr = (

let uu____16884 = (FStar_TypeChecker_Env.inst_tscheme_with repr_ts ((u)::[]))
in (FStar_All.pipe_right uu____16884 FStar_Pervasives_Native.snd))
in (

let uu____16893 = (

let uu____16898 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((a_tm)::is))
in (FStar_Syntax_Syntax.mk_Tm_app repr uu____16898))
in (uu____16893 FStar_Pervasives_Native.None r)))
end)
in ((uu____16799), (g)))
end))
end
| uu____16907 -> begin
(fail1 signature)
end))
end
| uu____16908 -> begin
(fail1 signature)
end))
end))))


let fresh_effect_repr_en : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t) = (fun env r eff_name u a_tm -> (

let uu____16939 = (FStar_All.pipe_right eff_name (FStar_TypeChecker_Env.get_effect_decl env))
in (FStar_All.pipe_right uu____16939 (fun ed -> (

let uu____16947 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr)
in (fresh_effect_repr env r eff_name ed.FStar_Syntax_Syntax.signature uu____16947 u a_tm))))))


let layered_effect_indices_as_binders : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders = (fun env r eff_name sig_ts u a_tm -> (

let uu____16983 = (FStar_TypeChecker_Env.inst_tscheme_with sig_ts ((u)::[]))
in (match (uu____16983) with
| (uu____16988, sig_tm) -> begin
(

let fail1 = (fun t -> (

let uu____16996 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env eff_name t)
in (FStar_Errors.raise_error uu____16996 r)))
in (

let uu____17002 = (

let uu____17003 = (FStar_Syntax_Subst.compress sig_tm)
in uu____17003.FStar_Syntax_Syntax.n)
in (match (uu____17002) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____17007) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a', uu____17030))::bs2 -> begin
(FStar_All.pipe_right bs2 (FStar_Syntax_Subst.subst_binders ((FStar_Syntax_Syntax.NT (((a'), (a_tm))))::[])))
end
| uu____17052 -> begin
(fail1 sig_tm)
end))
end
| uu____17053 -> begin
(fail1 sig_tm)
end)))
end)))


let lift_tf_layered_effect : FStar_Ident.lident  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun tgt lift_ts env c -> ((

let uu____17084 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____17084) with
| true -> begin
(

let uu____17089 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____17091 = (FStar_Syntax_Print.lid_to_string tgt)
in (FStar_Util.print2 "Lifting comp %s to layered effect %s {\n" uu____17089 uu____17091)))
end
| uu____17094 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let effect_args_from_repr = (fun repr is_layered1 -> (

let err = (fun uu____17121 -> (

let uu____17122 = (

let uu____17128 = (

let uu____17130 = (FStar_Syntax_Print.term_to_string repr)
in (

let uu____17132 = (FStar_Util.string_of_bool is_layered1)
in (FStar_Util.format2 "Could not get effect args from repr %s with is_layered %s" uu____17130 uu____17132)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____17128)))
in (FStar_Errors.raise_error uu____17122 r)))
in (

let repr1 = (FStar_Syntax_Subst.compress repr)
in (match (is_layered1) with
| true -> begin
(match (repr1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____17144, (uu____17145)::is) -> begin
(FStar_All.pipe_right is (FStar_List.map FStar_Pervasives_Native.fst))
end
| uu____17213 -> begin
(err ())
end)
end
| uu____17214 -> begin
(match (repr1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____17218, c1) -> begin
(

let uu____17240 = (FStar_All.pipe_right c1 FStar_Syntax_Util.comp_to_comp_typ)
in (FStar_All.pipe_right uu____17240 (fun ct -> (FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args (FStar_List.map FStar_Pervasives_Native.fst)))))
end
| uu____17275 -> begin
(err ())
end)
end))))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (

let uu____17277 = (

let uu____17288 = (FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs)
in (

let uu____17289 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____17288), (ct.FStar_Syntax_Syntax.result_typ), (uu____17289))))
in (match (uu____17277) with
| (u, a, c_is) -> begin
(

let uu____17337 = (FStar_TypeChecker_Env.inst_tscheme_with lift_ts ((u)::[]))
in (match (uu____17337) with
| (uu____17346, lift_t) -> begin
(

let lift_t_shape_error = (fun s -> (

let uu____17357 = (FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____17359 = (FStar_Ident.string_of_lid tgt)
in (

let uu____17361 = (FStar_Syntax_Print.term_to_string lift_t)
in (FStar_Util.format4 "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)" uu____17357 uu____17359 s uu____17361)))))
in (

let uu____17364 = (

let uu____17397 = (

let uu____17398 = (FStar_Syntax_Subst.compress lift_t)
in uu____17398.FStar_Syntax_Syntax.n)
in (match (uu____17397) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) when ((FStar_List.length bs) >= (Prims.parse_int "2")) -> begin
(

let uu____17462 = (FStar_Syntax_Subst.open_comp bs c1)
in (match (uu____17462) with
| ((a_b)::bs1, c2) -> begin
(

let uu____17522 = (FStar_All.pipe_right bs1 (FStar_List.splitAt ((FStar_List.length bs1) - (Prims.parse_int "1"))))
in (

let uu____17584 = (FStar_Syntax_Util.comp_to_comp_typ c2)
in ((a_b), (uu____17522), (uu____17584))))
end))
end
| uu____17611 -> begin
(

let uu____17612 = (

let uu____17618 = (lift_t_shape_error "either not an arrow or not enough binders")
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____17618)))
in (FStar_Errors.raise_error uu____17612 r))
end))
in (match (uu____17364) with
| (a_b, (rest_bs, (f_b)::[]), lift_ct) -> begin
(

let uu____17736 = (

let uu____17743 = (

let uu____17744 = (

let uu____17745 = (

let uu____17752 = (FStar_All.pipe_right a_b FStar_Pervasives_Native.fst)
in ((uu____17752), (a)))
in FStar_Syntax_Syntax.NT (uu____17745))
in (uu____17744)::[])
in (FStar_TypeChecker_Env.uvars_for_binders env rest_bs uu____17743 (fun b -> (

let uu____17769 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____17771 = (FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____17773 = (FStar_Ident.string_of_lid tgt)
in (

let uu____17775 = (FStar_Range.string_of_range r)
in (FStar_Util.format4 "implicit var for binder %s of %s~>%s at %s" uu____17769 uu____17771 uu____17773 uu____17775)))))) r))
in (match (uu____17736) with
| (rest_bs_uvars, g) -> begin
((

let uu____17789 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____17789) with
| true -> begin
(

let uu____17794 = (FStar_List.fold_left (fun s u1 -> (

let uu____17803 = (

let uu____17805 = (FStar_Syntax_Print.term_to_string u1)
in (Prims.op_Hat ";;;;" uu____17805))
in (Prims.op_Hat s uu____17803))) "" rest_bs_uvars)
in (FStar_Util.print1 "Introduced uvars: %s\n" uu____17794))
end
| uu____17810 -> begin
()
end));
(

let substs = (FStar_List.map2 (fun b t -> (

let uu____17836 = (

let uu____17843 = (FStar_All.pipe_right b FStar_Pervasives_Native.fst)
in ((uu____17843), (t)))
in FStar_Syntax_Syntax.NT (uu____17836))) ((a_b)::rest_bs) ((a)::rest_bs_uvars))
in (

let guard_f = (

let f_sort = (

let uu____17862 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort (FStar_Syntax_Subst.subst substs))
in (FStar_All.pipe_right uu____17862 FStar_Syntax_Subst.compress))
in (

let f_sort_is = (

let uu____17868 = (FStar_TypeChecker_Env.is_layered_effect env ct.FStar_Syntax_Syntax.effect_name)
in (effect_args_from_repr f_sort uu____17868))
in (FStar_List.fold_left2 (fun g1 i1 i2 -> (

let uu____17877 = (FStar_TypeChecker_Rel.teq env i1 i2)
in (FStar_TypeChecker_Env.conj_guard g1 uu____17877))) FStar_TypeChecker_Env.trivial_guard c_is f_sort_is)))
in (

let is = (

let uu____17881 = (FStar_TypeChecker_Env.is_layered_effect env tgt)
in (effect_args_from_repr lift_ct.FStar_Syntax_Syntax.result_typ uu____17881))
in (

let c1 = (

let uu____17884 = (

let uu____17885 = (

let uu____17896 = (FStar_All.pipe_right is (FStar_List.map (FStar_Syntax_Subst.subst substs)))
in (FStar_All.pipe_right uu____17896 (FStar_List.map FStar_Syntax_Syntax.as_arg)))
in {FStar_Syntax_Syntax.comp_univs = lift_ct.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = tgt; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = uu____17885; FStar_Syntax_Syntax.flags = ct.FStar_Syntax_Syntax.flags})
in (FStar_Syntax_Syntax.mk_Comp uu____17884))
in ((

let uu____17916 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____17916) with
| true -> begin
(

let uu____17921 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print1 "} Lifted comp: %s\n" uu____17921))
end
| uu____17924 -> begin
()
end));
(

let uu____17926 = (FStar_TypeChecker_Env.conj_guard g guard_f)
in ((c1), (uu____17926)));
)))));
)
end))
end)))
end))
end)))));
))


let lift_tf_layered_effect_term : 'Auu____17940 . 'Auu____17940  ->  FStar_Syntax_Syntax.sub_eff  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env sub1 u a e -> (

let lift = (

let uu____17969 = (

let uu____17974 = (FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must)
in (FStar_All.pipe_right uu____17974 (fun ts -> (FStar_TypeChecker_Env.inst_tscheme_with ts ((u)::[])))))
in (FStar_All.pipe_right uu____17969 FStar_Pervasives_Native.snd))
in (

let rest_bs = (

let lift_t = (FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp FStar_Util.must)
in (

let uu____18017 = (

let uu____18018 = (

let uu____18021 = (FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd)
in (FStar_All.pipe_right uu____18021 FStar_Syntax_Subst.compress))
in uu____18018.FStar_Syntax_Syntax.n)
in (match (uu____18017) with
| FStar_Syntax_Syntax.Tm_arrow ((uu____18044)::bs, uu____18046) when ((FStar_List.length bs) >= (Prims.parse_int "1")) -> begin
(

let uu____18086 = (FStar_All.pipe_right bs (FStar_List.splitAt ((FStar_List.length bs) - (Prims.parse_int "1"))))
in (FStar_All.pipe_right uu____18086 FStar_Pervasives_Native.fst))
end
| uu____18192 -> begin
(

let uu____18193 = (

let uu____18199 = (

let uu____18201 = (FStar_Syntax_Print.tscheme_to_string lift_t)
in (FStar_Util.format1 "lift_t tscheme %s is not an arrow with enough binders" uu____18201))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____18199)))
in (FStar_Errors.raise_error uu____18193 (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos))
end)))
in (

let args = (

let uu____18228 = (FStar_Syntax_Syntax.as_arg a)
in (

let uu____18237 = (

let uu____18248 = (FStar_All.pipe_right rest_bs (FStar_List.map (fun uu____18284 -> (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.unit_const))))
in (

let uu____18291 = (

let uu____18302 = (FStar_Syntax_Syntax.as_arg e)
in (uu____18302)::[])
in (FStar_List.append uu____18248 uu____18291)))
in (uu____18228)::uu____18237))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lift), (args)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))))


let get_mlift_for_subeff : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sub_eff  ->  FStar_TypeChecker_Env.mlift = (fun env sub1 -> (

let uu____18366 = ((FStar_TypeChecker_Env.is_layered_effect env sub1.FStar_Syntax_Syntax.source) || (FStar_TypeChecker_Env.is_layered_effect env sub1.FStar_Syntax_Syntax.target))
in (match (uu____18366) with
| true -> begin
(

let uu____18369 = (

let uu____18382 = (FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp FStar_Util.must)
in (lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____18382))
in {FStar_TypeChecker_Env.mlift_wp = uu____18369; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some ((lift_tf_layered_effect_term env sub1))})
end
| uu____18394 -> begin
(

let mk_mlift_wp = (fun ts env1 c -> (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (

let uu____18417 = (FStar_TypeChecker_Env.inst_tscheme_with ts ct.FStar_Syntax_Syntax.comp_univs)
in (match (uu____18417) with
| (uu____18426, lift_t) -> begin
(

let wp = (FStar_List.hd ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____18445 = (

let uu____18446 = (

let uu___2263_18447 = ct
in (

let uu____18448 = (

let uu____18459 = (

let uu____18468 = (

let uu____18469 = (

let uu____18476 = (

let uu____18477 = (

let uu____18494 = (

let uu____18505 = (FStar_Syntax_Syntax.as_arg ct.FStar_Syntax_Syntax.result_typ)
in (uu____18505)::(wp)::[])
in ((lift_t), (uu____18494)))
in FStar_Syntax_Syntax.Tm_app (uu____18477))
in (FStar_Syntax_Syntax.mk uu____18476))
in (uu____18469 FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_right uu____18468 FStar_Syntax_Syntax.as_arg))
in (uu____18459)::[])
in {FStar_Syntax_Syntax.comp_univs = uu___2263_18447.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = sub1.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.result_typ = uu___2263_18447.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____18448; FStar_Syntax_Syntax.flags = uu___2263_18447.FStar_Syntax_Syntax.flags}))
in (FStar_Syntax_Syntax.mk_Comp uu____18446))
in ((uu____18445), (FStar_TypeChecker_Common.trivial_guard))))
end))))
in (

let mk_mlift_term = (fun ts u r e -> (

let uu____18605 = (FStar_TypeChecker_Env.inst_tscheme_with ts ((u)::[]))
in (match (uu____18605) with
| (uu____18612, lift_t) -> begin
(

let uu____18614 = (

let uu____18621 = (

let uu____18622 = (

let uu____18639 = (

let uu____18650 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____18659 = (

let uu____18670 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____18679 = (

let uu____18690 = (FStar_Syntax_Syntax.as_arg e)
in (uu____18690)::[])
in (uu____18670)::uu____18679))
in (uu____18650)::uu____18659))
in ((lift_t), (uu____18639)))
in FStar_Syntax_Syntax.Tm_app (uu____18622))
in (FStar_Syntax_Syntax.mk uu____18621))
in (uu____18614 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end)))
in (

let uu____18743 = (

let uu____18756 = (FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp FStar_Util.must)
in (FStar_All.pipe_right uu____18756 mk_mlift_wp))
in {FStar_TypeChecker_Env.mlift_wp = uu____18743; FStar_TypeChecker_Env.mlift_term = (match (sub1.FStar_Syntax_Syntax.lift) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some ((fun uu____18792 uu____18793 e -> (FStar_Util.return_all e)))
end
| FStar_Pervasives_Native.Some (ts) -> begin
FStar_Pervasives_Native.Some ((mk_mlift_term ts))
end)})))
end)))


let get_field_projector_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env datacon index1 -> (

let uu____18823 = (FStar_TypeChecker_Env.lookup_datacon env datacon)
in (match (uu____18823) with
| (uu____18828, t) -> begin
(

let err = (fun n1 -> (

let uu____18838 = (

let uu____18844 = (

let uu____18846 = (FStar_Ident.string_of_lid datacon)
in (

let uu____18848 = (FStar_Util.string_of_int n1)
in (

let uu____18850 = (FStar_Util.string_of_int index1)
in (FStar_Util.format3 "Data constructor %s does not have enough binders (has %s, tried %s)" uu____18846 uu____18848 uu____18850))))
in ((FStar_Errors.Fatal_UnexpectedDataConstructor), (uu____18844)))
in (

let uu____18854 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____18838 uu____18854))))
in (

let uu____18855 = (

let uu____18856 = (FStar_Syntax_Subst.compress t)
in uu____18856.FStar_Syntax_Syntax.n)
in (match (uu____18855) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____18860) -> begin
(

let bs1 = (FStar_All.pipe_right bs (FStar_List.filter (fun uu____18915 -> (match (uu____18915) with
| (uu____18923, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
false
end
| uu____18932 -> begin
true
end)
end))))
in (match (((FStar_List.length bs1) <= index1)) with
| true -> begin
(err (FStar_List.length bs1))
end
| uu____18949 -> begin
(

let b = (FStar_List.nth bs1 index1)
in (

let uu____18964 = (FStar_Syntax_Util.mk_field_projector_name datacon (FStar_Pervasives_Native.fst b) index1)
in (FStar_All.pipe_right uu____18964 FStar_Pervasives_Native.fst)))
end))
end
| uu____18975 -> begin
(err (Prims.parse_int "0"))
end)))
end)))




